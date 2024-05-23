// Copyright 2019 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package protojson

import (
	"bytes"
	"encoding/base64"
	jsonstd "encoding/json"
	"fmt"
	"math"
	"reflect"
	"strconv"
	"strings"

	"github.com/fatih/structtag"
	"github.com/gogo/protobuf/jsonpb"
	gogoproto "github.com/gogo/protobuf/proto"
	"google.golang.org/protobuf/encoding/protowire"
	"google.golang.org/protobuf/internal/encoding/json"
	"google.golang.org/protobuf/internal/encoding/messageset"
	"google.golang.org/protobuf/internal/errors"
	"google.golang.org/protobuf/internal/flags"
	"google.golang.org/protobuf/internal/genid"
	"google.golang.org/protobuf/internal/pragma"
	"google.golang.org/protobuf/internal/set"
	"google.golang.org/protobuf/proto"
	"google.golang.org/protobuf/reflect/protoreflect"
	"google.golang.org/protobuf/reflect/protoregistry"
)

// Unmarshal reads the given []byte into the given [proto.Message].
// The provided message must be mutable (e.g., a non-nil pointer to a message).
func Unmarshal(b []byte, m proto.Message) error {
	return UnmarshalOptions{}.Unmarshal(b, m)
}

// UnmarshalOptions is a configurable JSON format parser.
type UnmarshalOptions struct {
	pragma.NoUnkeyedLiterals

	// If AllowPartial is set, input for messages that will result in missing
	// required fields will not return an error.
	AllowPartial bool

	// If DiscardUnknown is set, unknown fields and enum name values are ignored.
	DiscardUnknown bool

	// Resolver is used for looking up types when unmarshaling
	// google.protobuf.Any messages or extension fields.
	// If nil, this defaults to using protoregistry.GlobalTypes.
	Resolver interface {
		protoregistry.MessageTypeResolver
		protoregistry.ExtensionTypeResolver
	}

	// RecursionLimit limits how deeply messages may be nested.
	// If zero, a default limit is applied.
	RecursionLimit int
}

// Unmarshal reads the given []byte and populates the given [proto.Message]
// using options in the UnmarshalOptions object.
// It will clear the message first before setting the fields.
// If it returns an error, the given message may be partially set.
// The provided message must be mutable (e.g., a non-nil pointer to a message).
func (o UnmarshalOptions) Unmarshal(b []byte, m any) error {
	return o.unmarshal(b, m)
}

// unmarshal is a centralized function that all unmarshal operations go through.
// For profiling purposes, avoid changing the name of this function or
// introducing other code paths for unmarshal that do not go through this.
func (o UnmarshalOptions) unmarshal(b []byte, msg any) error {
	valueProto, isProto := msg.(proto.Message)
	if isProto {
		proto.Reset(valueProto)
	}

	if o.Resolver == nil {
		o.Resolver = protoregistry.GlobalTypes
	}
	if o.RecursionLimit == 0 {
		o.RecursionLimit = protowire.DefaultRecursionLimit
	}

	dec := decoder{json.NewDecoder(b), o}
	if err := dec.unmarshalMessage(msg, false); err != nil {
		return err
	}

	// Check for EOF.
	tok, err := dec.Read()
	if err != nil {
		return err
	}
	if tok.Kind() != json.EOF {
		return dec.unexpectedTokenError(tok)
	}

	if o.AllowPartial {
		return nil
	}
	if isProto {
		return proto.CheckInitialized(valueProto)
	}
	return nil
}

type decoder struct {
	*json.Decoder
	opts UnmarshalOptions
}

// newError returns an error object with position info.
func (d decoder) newError(pos int, f string, x ...any) error {
	line, column := d.Position(pos)
	head := fmt.Sprintf("(line %d:%d): ", line, column)
	return errors.New(head+f, x...)
}

// unexpectedTokenError returns a syntax error for the given unexpected token.
func (d decoder) unexpectedTokenError(tok json.Token) error {
	return d.syntaxError(tok.Pos(), "unexpected token %s", tok.RawString())
}

// syntaxError returns a syntax error for given position.
func (d decoder) syntaxError(pos int, f string, x ...any) error {
	line, column := d.Position(pos)
	head := fmt.Sprintf("syntax error (line %d:%d): ", line, column)
	return errors.New(head+f, x...)
}

// unmarshalMessage unmarshals a message into the given protoreflect.Message.
func (d decoder) unmarshalMessage(msg any, skipTypeURL bool) error {
	d.opts.RecursionLimit--
	if d.opts.RecursionLimit < 0 {
		return errors.New("exceeded max recursion depth")
	}

	value := reflect.ValueOf(msg)
	if value.Type().Kind() == reflect.Ptr {
		value = value.Elem()
	}

	valueGogoProto, isGogoProto := msg.(gogoproto.Message)
	valueProto, isProto := msg.(proto.Message)

	var m protoreflect.Message
	if isProto {
		m = valueProto.ProtoReflect()

		if unmarshal := wellKnownTypeUnmarshaler(m.Descriptor().FullName()); unmarshal != nil {
			return unmarshal(d, m)
		}
	}

	if !isProto {
		if isGogoProto {
			b, err := d.Decoder.ReadObject()
			if err != nil {
				return err
			}
			if pkgPath := value.Type().PkgPath(); strings.HasPrefix(pkgPath, "k8s.io/api/") || strings.HasPrefix(pkgPath, "k8s.io/apimachinery/") {
				return jsonstd.Unmarshal(b, msg)
			}
			return (&jsonpb.Unmarshaler{}).Unmarshal(bytes.NewReader(b), valueGogoProto)
		}
	}

	tok, err := d.Read()
	if err != nil {
		return err
	}
	if tok.Kind() != json.ObjectOpen {
		return d.unexpectedTokenError(tok)
	}

	messageDesc := m.Descriptor()
	if !flags.ProtoLegacy && messageset.IsMessageSet(messageDesc) {
		return errors.New("no support for proto1 MessageSets")
	}

	var seenNums set.Ints
	var seenOneofs set.Ints
	fieldDescs := messageDesc.Fields()
	for {
		// Read field name.
		tok, err := d.Read()
		if err != nil {
			return err
		}
		switch tok.Kind() {
		default:
			return d.unexpectedTokenError(tok)
		case json.ObjectClose:
			return nil
		case json.Name:
			// Continue below.
		}

		name := tok.Name()
		// Unmarshaling a non-custom embedded message in Any will contain the
		// JSON field "@type" which should be skipped because it is not a field
		// of the embedded message, but simply an artifact of the Any format.
		if skipTypeURL && name == "@type" {
			d.Read()
			continue
		}

		// Get the FieldDescriptor.
		var fd protoreflect.FieldDescriptor
		if strings.HasPrefix(name, "[") && strings.HasSuffix(name, "]") {
			// Only extension names are in [name] format.
			extName := protoreflect.FullName(name[1 : len(name)-1])
			extType, err := d.opts.Resolver.FindExtensionByName(extName)
			if err != nil && err != protoregistry.NotFound {
				return d.newError(tok.Pos(), "unable to resolve %s: %v", tok.RawString(), err)
			}
			if extType != nil {
				fd = extType.TypeDescriptor()
				if !messageDesc.ExtensionRanges().Has(fd.Number()) || fd.ContainingMessage().FullName() != messageDesc.FullName() {
					return d.newError(tok.Pos(), "message %v cannot be extended by %v", messageDesc.FullName(), fd.FullName())
				}
			}
		} else {
			// The name can either be the JSON name or the proto field name.
			fd = fieldDescs.ByJSONName(name)
			if fd == nil {
				fd = fieldDescs.ByTextName(name)
			}
		}
		if flags.ProtoLegacy {
			if fd != nil && fd.IsWeak() && fd.Message().IsPlaceholder() {
				fd = nil // reset since the weak reference is not linked in
			}
		}

		if fd == nil {
			// Field is unknown.
			if d.opts.DiscardUnknown {
				if err := d.skipJSONValue(); err != nil {
					return err
				}
				continue
			}
			return d.newError(tok.Pos(), "unknown field %v", tok.RawString())
		}

		// Do not allow duplicate fields.
		num := uint64(fd.Number())
		if seenNums.Has(num) {
			return d.newError(tok.Pos(), "duplicate field %v", tok.RawString())
		}
		seenNums.Set(num)

		// No need to set values for JSON null unless the field type is
		// google.protobuf.Value or google.protobuf.NullValue.
		if tok, _ := d.Peek(); tok.Kind() == json.Null && !isKnownValue(fd) && !isNullValue(fd) {
			d.Read()
			continue
		}

		switch {
		case fd.IsList():
			f := value.FieldByNameFunc(func(n string) bool {
				f, ok := value.Type().FieldByName(n)
				if !ok {
					return false
				}
				tags, err := structtag.Parse(string(f.Tag))
				if err != nil {
					return false
				}
				pbtag, err := tags.Get("protobuf")
				if err != nil {
					return false
				}
				for _, opt := range pbtag.Options {
					if !strings.HasPrefix(opt, "name=") {
						continue
					}
					pbname := strings.TrimPrefix(opt, "name=")
					if pbname == fd.TextName() {
						return true
					}
				}
				return false
			})
			if !f.IsValid() {
				return fmt.Errorf("unable to find field with protobuf tag that includes 'name=%s'", fd.TextName())
			}
			if f.Type().Kind() != reflect.Slice {
				return fmt.Errorf("expected dst of type slice, got %s", f.Type().Kind().String())
			}
			val := reflect.New(f.Type())
			if err := d.unmarshalList(val.Interface(), fd); err != nil {
				return err
			}
			f.Set(val.Elem())
		case fd.IsMap():
			f := value.FieldByNameFunc(func(n string) bool {
				f, ok := value.Type().FieldByName(n)
				if !ok {
					return false
				}
				tags, err := structtag.Parse(string(f.Tag))
				if err != nil {
					return false
				}
				pbtag, err := tags.Get("protobuf")
				if err != nil {
					return false
				}
				for _, opt := range pbtag.Options {
					if !strings.HasPrefix(opt, "name=") {
						continue
					}
					pbname := strings.TrimPrefix(opt, "name=")
					if pbname == fd.TextName() {
						return true
					}
				}
				return false
			})
			if !f.IsValid() {
				return fmt.Errorf("unable to find field with protobuf tag that includes 'name=%s'", fd.TextName())
			}
			if f.Type().Kind() != reflect.Map {
				return fmt.Errorf("expected dst of type map, got %s", f.Type().Kind().String())
			}
			f.Set(reflect.MakeMap(f.Type()))
			if err := d.unmarshalMap(f.Interface(), fd); err != nil {
				return err
			}
		default:
			// If field is a oneof, check if it has already been set.
			if od := fd.ContainingOneof(); od != nil {
				idx := uint64(od.Index())
				if seenOneofs.Has(idx) {
					return d.newError(tok.Pos(), "error parsing %s, oneof %v is already set", tok.RawString(), od.FullName())
				}
				seenOneofs.Set(idx)
			}

			// Required or optional fields.
			if err := d.unmarshalSingular(msg, fd); err != nil {
				return err
			}
		}
	}
}

func isKnownValue(fd protoreflect.FieldDescriptor) bool {
	md := fd.Message()
	return md != nil && md.FullName() == genid.Value_message_fullname
}

func isNullValue(fd protoreflect.FieldDescriptor) bool {
	ed := fd.Enum()
	return ed != nil && ed.FullName() == genid.NullValue_enum_fullname
}

// unmarshalSingular unmarshals to the non-repeated field specified
// by the given FieldDescriptor.
func (d decoder) unmarshalSingular(m any, fd protoreflect.FieldDescriptor) error {
	value := reflect.ValueOf(m)
	if value.Type().Kind() == reflect.Ptr {
		value = value.Elem()
	}

	f := value.FieldByNameFunc(func(n string) bool {
		f, ok := value.Type().FieldByName(n)
		if !ok {
			return false
		}
		tags, err := structtag.Parse(string(f.Tag))
		if err != nil {
			return false
		}
		pbtag, err := tags.Get("protobuf")
		if err != nil {
			return false
		}
		for _, opt := range pbtag.Options {
			if !strings.HasPrefix(opt, "name=") {
				continue
			}
			pbname := strings.TrimPrefix(opt, "name=")
			if pbname == fd.TextName() {
				return true
			}
		}
		return false
	})
	if !f.IsValid() {
		return fmt.Errorf("unable to find field with protobuf tag that includes 'name=%s'", fd.TextName())
	}

	var val any
	var err error
	switch fd.Kind() {
	case protoreflect.MessageKind, protoreflect.GroupKind:

		val = reflect.New(f.Type().Elem()).Interface()
		err = d.unmarshalMessage(val, false)
	default:
		val, err = d.unmarshalScalar(fd)
	}

	if err != nil {
		return err
	}
	f.Set(reflect.ValueOf(val))
	return nil
}

// unmarshalScalar unmarshals to a scalar/enum protoreflect.Value specified by
// the given FieldDescriptor.
func (d decoder) unmarshalScalar(fd protoreflect.FieldDescriptor) (any, error) {
	const b32 int = 32
	const b64 int = 64

	tok, err := d.Read()
	if err != nil {
		return protoreflect.Value{}, err
	}

	kind := fd.Kind()
	switch kind {
	case protoreflect.BoolKind:
		if tok.Kind() == json.Bool {
			return tok.Bool(), nil
		}

	case protoreflect.Int32Kind, protoreflect.Sint32Kind, protoreflect.Sfixed32Kind:
		if v, ok := unmarshalInt(tok, b32); ok {
			return v, nil
		}

	case protoreflect.Int64Kind, protoreflect.Sint64Kind, protoreflect.Sfixed64Kind:
		if v, ok := unmarshalInt(tok, b64); ok {
			return v, nil
		}

	case protoreflect.Uint32Kind, protoreflect.Fixed32Kind:
		if v, ok := unmarshalUint(tok, b32); ok {
			return v, nil
		}

	case protoreflect.Uint64Kind, protoreflect.Fixed64Kind:
		if v, ok := unmarshalUint(tok, b64); ok {
			return v, nil
		}

	case protoreflect.FloatKind:
		if v, ok := unmarshalFloat(tok, b32); ok {
			return v, nil
		}

	case protoreflect.DoubleKind:
		if v, ok := unmarshalFloat(tok, b64); ok {
			return v, nil
		}

	case protoreflect.StringKind:
		if tok.Kind() == json.String {
			return tok.ParsedString(), nil
		}

	case protoreflect.BytesKind:
		if v, ok := unmarshalBytes(tok); ok {
			return v, nil
		}

	case protoreflect.EnumKind:
		if v, ok := unmarshalEnum(tok, fd, d.opts.DiscardUnknown); ok {
			return v, nil
		}

	default:
		panic(fmt.Sprintf("unmarshalScalar: invalid scalar kind %v", kind))
	}

	return nil, d.newError(tok.Pos(), "invalid value for %v type: %v", kind, tok.RawString())
}

func unmarshalInt(tok json.Token, bitSize int) (any, bool) {
	switch tok.Kind() {
	case json.Number:
		return getInt(tok, bitSize)

	case json.String:
		// Decode number from string.
		s := strings.TrimSpace(tok.ParsedString())
		if len(s) != len(tok.ParsedString()) {
			return nil, false
		}
		dec := json.NewDecoder([]byte(s))
		tok, err := dec.Read()
		if err != nil {
			return nil, false
		}
		return getInt(tok, bitSize)
	}
	return nil, false
}

func getInt(tok json.Token, bitSize int) (any, bool) {
	n, ok := tok.Int(bitSize)
	if !ok {
		return nil, false
	}
	if bitSize == 32 {
		return int32(n), true
	}
	return n, true
}

func unmarshalUint(tok json.Token, bitSize int) (any, bool) {
	switch tok.Kind() {
	case json.Number:
		return getUint(tok, bitSize)

	case json.String:
		// Decode number from string.
		s := strings.TrimSpace(tok.ParsedString())
		if len(s) != len(tok.ParsedString()) {
			return nil, false
		}
		dec := json.NewDecoder([]byte(s))
		tok, err := dec.Read()
		if err != nil {
			return nil, false
		}
		return getUint(tok, bitSize)
	}
	return nil, false
}

func getUint(tok json.Token, bitSize int) (any, bool) {
	n, ok := tok.Uint(bitSize)
	if !ok {
		return nil, false
	}
	if bitSize == 32 {
		return uint32(n), true
	}
	return n, true
}

func unmarshalFloat(tok json.Token, bitSize int) (any, bool) {
	switch tok.Kind() {
	case json.Number:
		return getFloat(tok, bitSize)

	case json.String:
		s := tok.ParsedString()
		switch s {
		case "NaN":
			if bitSize == 32 {
				return float32(math.NaN()), true
			}
			return math.NaN(), true
		case "Infinity":
			if bitSize == 32 {
				return float32(math.Inf(+1)), true
			}
			return math.Inf(+1), true
		case "-Infinity":
			if bitSize == 32 {
				return float32(math.Inf(-1)), true
			}
			return math.Inf(-1), true
		}

		// Decode number from string.
		if len(s) != len(strings.TrimSpace(s)) {
			return nil, false
		}
		dec := json.NewDecoder([]byte(s))
		tok, err := dec.Read()
		if err != nil {
			return nil, false
		}
		return getFloat(tok, bitSize)
	}
	return nil, false
}

func getFloat(tok json.Token, bitSize int) (any, bool) {
	n, ok := tok.Float(bitSize)
	if !ok {
		return protoreflect.Value{}, false
	}
	if bitSize == 32 {
		return float32(n), true
	}
	return n, true
}

func unmarshalBytes(tok json.Token) (any, bool) {
	if tok.Kind() != json.String {
		return nil, false
	}

	s := tok.ParsedString()
	enc := base64.StdEncoding
	if strings.ContainsAny(s, "-_") {
		enc = base64.URLEncoding
	}
	if len(s)%4 != 0 {
		enc = enc.WithPadding(base64.NoPadding)
	}
	b, err := enc.DecodeString(s)
	if err != nil {
		return nil, false
	}
	return b, true
}

func unmarshalEnum(tok json.Token, fd protoreflect.FieldDescriptor, discardUnknown bool) (any, bool) {
	switch tok.Kind() {
	case json.String:
		// Lookup EnumNumber based on name.
		s := tok.ParsedString()
		if enumVal := fd.Enum().Values().ByName(protoreflect.Name(s)); enumVal != nil {
			return enumVal.Number(), true
		}
		if discardUnknown {
			return nil, true
		}

	case json.Number:
		if n, ok := tok.Int(32); ok {
			return protoreflect.EnumNumber(n), true
		}

	case json.Null:
		// This is only valid for google.protobuf.NullValue.
		if isNullValue(fd) {
			return protoreflect.EnumNumber(0), true
		}
	}

	return nil, false
}

func (d decoder) unmarshalList(m any, fd protoreflect.FieldDescriptor) error {
	tok, err := d.Read()
	if err != nil {
		return err
	}
	if tok.Kind() != json.ArrayOpen {
		return d.unexpectedTokenError(tok)
	}

	value := reflect.ValueOf(m)
	if value.Type().Kind() == reflect.Ptr {
		value = value.Elem()
	}

	switch fd.Kind() {
	case protoreflect.MessageKind, protoreflect.GroupKind:
		for {
			tok, err := d.Peek()
			if err != nil {
				return err
			}

			if tok.Kind() == json.ArrayClose {
				d.Read()
				return nil
			}
			var val reflect.Value
			t := value.Type().Elem()
			if t.Kind() == reflect.Ptr {
				val = reflect.New(t.Elem())
			} else {
				val = reflect.New(t)
			}
			if err := d.unmarshalMessage(val.Interface(), false); err != nil {
				return err
			}
			value.Set(reflect.Append(value, val))
		}
	default:
		for {
			tok, err := d.Peek()
			if err != nil {
				return err
			}

			if tok.Kind() == json.ArrayClose {
				d.Read()
				return nil
			}

			val, err := d.unmarshalScalar(fd)
			if err != nil {
				return err
			}
			value.Set(reflect.Append(value, reflect.ValueOf(val)))
		}
	}
}

func (d decoder) unmarshalMap(m any, fd protoreflect.FieldDescriptor) error {
	tok, err := d.Read()
	if err != nil {
		return err
	}
	if tok.Kind() != json.ObjectOpen {
		return d.unexpectedTokenError(tok)
	}

	value := reflect.ValueOf(m)
	if value.Type().Kind() != reflect.Map {
		return fmt.Errorf("unable to unmarshal map into type %T", m)
	}

	// Determine ahead whether map entry is a scalar type or a message type in
	// order to call the appropriate unmarshalMapValue func inside the for loop
	// below.
	var unmarshalMapValue func() (reflect.Value, error)
	switch fd.MapValue().Kind() {
	case protoreflect.MessageKind, protoreflect.GroupKind:
		unmarshalMapValue = func() (reflect.Value, error) {
			val := reflect.New(value.Elem().Type()).Interface()
			if err := d.unmarshalMessage(val, false); err != nil {
				return reflect.Value{}, err
			}
			return reflect.ValueOf(val), nil
		}
	default:
		unmarshalMapValue = func() (reflect.Value, error) {
			val, err := d.unmarshalScalar(fd.MapValue())
			if err != nil {
				return reflect.Value{}, err
			}
			return reflect.ValueOf(val), nil
		}
	}

Loop:
	for {
		// Read field name.
		tok, err := d.Read()
		if err != nil {
			return err
		}
		switch tok.Kind() {
		default:
			return d.unexpectedTokenError(tok)
		case json.ObjectClose:
			break Loop
		case json.Name:
			// Continue.
		}

		// Unmarshal field name.
		pkey, err := d.unmarshalMapKey(tok, fd.MapKey())
		if err != nil {
			return err
		}

		// Check for duplicate field name.
		if value.MapIndex(pkey).IsValid() {
			return d.newError(tok.Pos(), "duplicate map key %v", tok.RawString())
		}

		// Read and unmarshal field value.
		pval, err := unmarshalMapValue()
		if err != nil {
			return err
		}
		value.SetMapIndex(pkey, pval)
	}

	return nil
}

// unmarshalMapKey converts given token of Name kind into a protoreflect.MapKey.
// A map key type is any integral or string type.
func (d decoder) unmarshalMapKey(tok json.Token, fd protoreflect.FieldDescriptor) (reflect.Value, error) {
	const b32 = 32
	const b64 = 64
	const base10 = 10

	name := tok.Name()
	kind := fd.Kind()
	switch kind {
	case protoreflect.StringKind:
		return reflect.ValueOf(name), nil

	case protoreflect.BoolKind:
		switch name {
		case "true":
			return reflect.ValueOf(true), nil
		case "false":
			return reflect.ValueOf(false), nil
		}

	case protoreflect.Int32Kind, protoreflect.Sint32Kind, protoreflect.Sfixed32Kind:
		if n, err := strconv.ParseInt(name, base10, b32); err == nil {
			return reflect.ValueOf(int32(n)), nil
		}

	case protoreflect.Int64Kind, protoreflect.Sint64Kind, protoreflect.Sfixed64Kind:
		if n, err := strconv.ParseInt(name, base10, b64); err == nil {
			return reflect.ValueOf(int64(n)), nil
		}

	case protoreflect.Uint32Kind, protoreflect.Fixed32Kind:
		if n, err := strconv.ParseUint(name, base10, b32); err == nil {
			return reflect.ValueOf(uint32(n)), nil
		}

	case protoreflect.Uint64Kind, protoreflect.Fixed64Kind:
		if n, err := strconv.ParseUint(name, base10, b64); err == nil {
			return reflect.ValueOf(uint64(n)), nil
		}

	default:
		panic(fmt.Sprintf("invalid kind for map key: %v", kind))
	}

	return reflect.Value{}, d.newError(tok.Pos(), "invalid value for %v key: %s", kind, tok.RawString())
}

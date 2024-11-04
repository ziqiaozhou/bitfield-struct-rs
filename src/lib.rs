// Generate docs from readme
#![doc = include_str!("../README.md")]
#![warn(clippy::unwrap_used)]

use proc_macro as pc;
use proc_macro2::{Ident, TokenStream};
use quote::{format_ident, quote, ToTokens};
use std::{fmt, stringify};
use syn::parse::{Parse, ParseStream};
use syn::spanned::Spanned;
use syn::{Token, Attribute};

fn s_err(span: proc_macro2::Span, msg: impl fmt::Display) -> syn::Error {
    syn::Error::new(span, msg)
}

/// Creates a bitfield for this struct.
///
/// The arguments first, have to begin with the underlying type of the bitfield:
/// For example: `#[bitfield(u64)]`.
///
/// It can contain an extra `debug` argument for disabling the `Debug` trait
/// generation (`#[bitfield(u64, debug = false)]`).
///
/// Parameters of the `bitfield` attribute:
/// - the bitfield type
/// - `debug` to disable the `Debug` trait generation
/// - `default` to disable the `Default` trait generation
/// - `order` to specify the bit order (Lsb, Msb)
/// - `conversion` to disable the generation of into_bits and from_bits
///
/// Parameters of the `bits` attribute (for fields):
/// - the number of bits
/// - `access` to specify the access mode (RW, RO, WO, None)
/// - `default` to set a default value
/// - `into` to specify a conversion function from the field type to the bitfield type
/// - `from` to specify a conversion function from the bitfield type to the field type
/*#[proc_macro_attribute]
pub fn bitfield(args: pc::TokenStream, input: pc::TokenStream) -> pc::TokenStream {
    match bitfield_inner(args.into(), input.into()) {
        Ok(result) => result.into(),
        Err(e) => e.into_compile_error().into(),
    }
}*/

#[proc_macro_attribute]
pub fn bitfield_spec(args: pc::TokenStream, input: pc::TokenStream) -> pc::TokenStream {
    match bitfield_inner_spec(args.into(), input.into()) {
        Ok(result) => {
            result.into()
        }
        Err(e) => e.into_compile_error().into(),
    }
}

fn find_attr<'a>(attrs: &'a [Attribute], name: &str) -> Option<&'a Attribute> {
    attrs.iter().find(|attr| !attr.path().segments.is_empty() && attr.path().segments[0].ident == name)
}

fn bitfield_inner_spec(args: TokenStream, input: TokenStream) -> syn::Result<TokenStream> {
    let input = syn::parse2::<syn::ItemStruct>(input)?;
    let input_copy = input.clone();
    let SpecParams {spec_only, externals} = syn::parse2(args)?;

    let span = input.fields.span();
    let name = input.ident;
    let name_lower = name.to_string().to_lowercase();
    let spec_name = format_ident!("Spec{}", name);

    let vis = input.vis;
    let open_close = if vis == syn::Visibility::Inherited {
        quote!{closed}
    } else {
        quote!{open}
    };

    let bitfield = find_attr(&input.attrs, "bitfield").expect("Must have a bitfield attr.");
    let Params {
        ty,
        bits,
        default,
        order,
        conversion,
        ..
    } = bitfield.parse_args()?;
    let syn::Fields::Named(fields) = input.fields else {
        return Err(s_err(span, "only named fields are supported"));
    };
    let repr = ty.clone();

    let mut offset = 0;
    let mut members = Vec::with_capacity(fields.named.len());
    for field in fields.named {
        let f = Member::new(
            ty.clone(),
            bits,
            field,
            offset,
            order,
        )?;
        offset += f.bits;
        members.push(f);
    }
    let all_idents = members.iter().map(Member::ident).collect::<Vec<_>>();


    if offset < bits {
        return Err(s_err(
            span,
            format!(
                "The bitfield size ({bits} bits) has to be equal to the sum of its members ({offset} bits)!. \
                You might have to add padding (a {} bits large member prefixed with \"_\").",
                bits - offset
            ),
        ));
    }
    if offset > bits {
        return Err(s_err(
            span,
            format!(
                "The size of the members ({offset} bits) is larger than the type ({bits} bits)!."
            ),
        ));
    }

    let spec_defaults = members.iter().map(Member::spec_default).collect::<Vec<_>>();

    let impl_new = quote! {
            /// Creates a new default initialized bitfield.
            pub open spec fn new() -> Self {
                Self::default()
            }
        };

    let impl_default = if default {
        quote! {
            impl #spec_name {
                #[allow(clippy::assign_op_pattern)]
                pub closed spec fn default() -> Self {
                    let this = Self(0);
                    #( #spec_defaults )*
                    this
                }
            }
        }
    } else {
        quote!{}
    };

    let conversion = conversion.then(|| {
        quote! {
            /// Convert from bits.
            #vis #open_close spec fn spec_from_bits(bits: #repr) -> Self {
                Self(bits)
            }
            /// Convert into bits.
            #vis #open_close spec fn spec_into_bits(self) -> #repr {
                self.0
            }
        }
    });

    let external_types = externals.iter().map(|e| e.ty.clone()).collect();

    let spec_members = members.iter().enumerate().map(|(i, m)|{let mut others = all_idents.clone(); others.remove(i); m.to_spec(others, &name, &external_types)}).collect::<Vec<_>>();
    let to_external_spec = if !spec_only {
        members
        .iter()
        .map(|m| m.to_external_spec(&name, &spec_name))
        .collect::<Vec<_>>()
    } else {
        vec![]
    };
    let ex_new = format_ident!("ex_{}_new", name_lower);
    let ex_default = format_ident!("ex_{}_default", name_lower);
    let _modname = format_ident!("mod_{}", name_lower);
    let external_types = externals.iter().map(|e|gen_external_types(&spec_name, &ty, &e.ty, e.bits));
    let exe_code = if !spec_only {
        quote!{
            #[verus_verify]
            #input_copy
            builtin_macros::verus!{
            impl vstd::prelude::View for #name {
                type V = #spec_name;
                closed spec fn view(&self) -> Self::V {
                    #spec_name(self.0)
                }
            }
            #[verifier(external_fn_specification)]
            pub fn #ex_new() -> (ret: #name)
            ensures
                ::builtin::equal(ret@, #spec_name::new())
            {
                #name::new()
            }
            #[verifier(external_fn_specification)]
            pub fn #ex_default() -> (ret: #name)
            ensures
                ::builtin::equal(ret@, #spec_name::new())
            {
                #name::default()
            }
            impl verify_external::convert::FromSpec<#repr> for #name {
                closed spec fn from_spec(v: #repr) -> Self {
                    Self(v)
                }
            }
            impl verify_external::convert::FromSpec<#name> for #repr {
                closed spec fn from_spec(v: #name) -> #repr {
                    v.0
                }
            }
        }
        }
    } else {
        quote!{}
    };
    Ok(quote! {
        #exe_code
        builtin_macros::verus!{
        #[repr(transparent)]
        #vis ghost struct #spec_name(pub #repr);

        impl #spec_name {
            #impl_new

            #conversion

        }
        #( #spec_members )*

        #impl_default

        #( #to_external_spec )*
        #( #external_types )*
    }}
    )
}

fn gen_external_types(_spec_name: &Ident, base_ty: &syn::Type, ty: &syn::Type, bits: usize) -> TokenStream {
    let name = if let syn::Type::Path(p) =  ty {
        p.path.get_ident().unwrap().to_string()
    } else {
        panic!("external must be a Type::Path.");
    };
    let name_lower = name.to_lowercase();
    let spec_from_bits = format_ident!("spec_{}_from_bits", name_lower);
    let spec_into_bits = format_ident!("spec_{}_into_bits", name_lower);
    let axiom_into_from = format_ident!("axiom_{}_into_from_bits", name_lower);
    let ex_into_bits = format_ident!("ex_{}_into_bits", name_lower);
    let ex_from_bits = format_ident!("ex_{}_from_bits", name_lower);
    quote!{
        pub spec fn #spec_from_bits(bits: #base_ty) -> #ty;
        pub spec fn #spec_into_bits(val: #ty) -> #base_ty;
        pub proof fn #axiom_into_from(val: #ty)
        ensures
            ::builtin::equal(#spec_from_bits(#spec_into_bits(val)), val),
            #spec_into_bits(val) < ((1 as #base_ty) << (#bits as #base_ty)),
        {
            admit()
        }
        #[verifier(external_fn_specification)]
        #[verifier::when_used_as_spec(#spec_from_bits)]
        pub fn #ex_from_bits(bits: #base_ty) -> (ret: #ty)
        ensures
            builtin::equal(ret, #spec_from_bits(bits))
        {
            #ty::from_bits(bits)
        }
        #[verifier(external_fn_specification)]
        #[verifier::when_used_as_spec(#spec_into_bits)]
        pub fn #ex_into_bits(val: #ty) -> (ret: #base_ty)
        ensures
            builtin::equal(ret, #spec_into_bits(val))
        {
            val.into_bits()
        }
    }
}

#[allow(dead_code)]
fn bitfield_inner(args: TokenStream, input: TokenStream) -> syn::Result<TokenStream> {
    let input = syn::parse2::<syn::ItemStruct>(input)?;
    let Params {
        ty,
        bits,
        debug,
        default,
        order,
        conversion,
    } = syn::parse2::<Params>(args)?;

    let span = input.fields.span();
    let name = input.ident;
    let vis = input.vis;
    let attrs: TokenStream = input.attrs.iter().map(ToTokens::to_token_stream).collect();

    let syn::Fields::Named(fields) = input.fields else {
        return Err(s_err(span, "only named fields are supported"));
    };

    let mut offset = 0;
    let mut members = Vec::with_capacity(fields.named.len());
    for field in fields.named {
        let f = Member::new(ty.clone(), bits, field, offset, order)?;
        offset += f.bits;
        members.push(f);
    }

    if offset < bits {
        return Err(s_err(
            span,
            format!(
                "The bitfield size ({bits} bits) has to be equal to the sum of its members ({offset} bits)!. \
                You might have to add padding (a {} bits large member prefixed with \"_\").",
                bits - offset
            ),
        ));
    }
    if offset > bits {
        return Err(s_err(
            span,
            format!(
                "The size of the members ({offset} bits) is larger than the type ({bits} bits)!."
            ),
        ));
    }

    let debug_impl = if debug {
        let debug_fields = members.iter().map(Member::debug);
        quote! {
            impl core::fmt::Debug for #name {
                fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                    f.debug_struct(stringify!(#name))
                        #( #debug_fields )*
                        .finish()
                }
            }
        }
    } else {
        quote!()
    };

    let defaults = members.iter().map(Member::default);

    let default_impl = if default {
        quote! {
            impl Default for #name {
                fn default() -> Self {
                    Self::new()
                }
            }
        }
    } else {
        quote!()
    };

    let conversion = if conversion {
        quote! {
            /// Convert from bits.
            #vis const fn from_bits(bits: #ty) -> Self {
                Self(bits)
            }
            /// Convert into bits.
            #vis const fn into_bits(self) -> #ty {
                self.0
            }
        }
    } else {
        quote!()
    };

    Ok(quote! {
        #attrs
        #[derive(Copy, Clone)]
        #[repr(transparent)]
        #vis struct #name(#ty);

        impl #name {
            /// Creates a new default initialized bitfield.
            #vis const fn new() -> Self {
                let mut this = Self(0);
                #( #defaults )*
                this
            }
            #conversion

            #( #members )*
        }

        #default_impl

        impl From<#ty> for #name {
            fn from(v: #ty) -> Self {
                Self(v)
            }
        }
        impl From<#name> for #ty {
            fn from(v: #name) -> #ty {
                v.0
            }
        }

        #debug_impl
    })
}

/// Represents a member where accessor functions should be generated for.
struct Member {
    offset: usize,
    bits: usize,
    base_ty: syn::Type,
    default: TokenStream,
    inner: Option<MemberInner>,
}

struct MemberInner {
    ident: syn::Ident,
    ty: syn::Type,
    attrs: Vec<syn::Attribute>,
    vis: syn::Visibility,
    into: TokenStream,
    from: TokenStream,
}

impl Member {
    fn ident(&self) -> Option<Ident> {
        self.inner.as_ref()?;
        let ident = self.inner.as_ref().unwrap().ident.clone();
        if ident.to_string().starts_with('_') {
            None
        } else {
            Some(ident)
        }
    }
}

impl Member {
    fn new(
        base_ty: syn::Type,
        base_bits: usize,
        f: syn::Field,
        offset: usize,
        order: Order,
    ) -> syn::Result<Self> {
        let span = f.span();

        let syn::Field {
            mut attrs,
            vis,
            ident,
            ty,
            ..
        } = f;

        let ident = ident.ok_or_else(|| s_err(span, "Not supported"))?;
        let ignore = ident.to_string().starts_with('_');

        let Field {
            bits,
            ty,
            mut default,
            into,
            from,
            access,
        } = parse_field(&base_ty, &attrs, &ty, ignore)?;

        let ignore = ignore || access == Access::None;

        if bits > 0 && !ignore {
            // overflow check
            if offset + bits > base_bits {
                return Err(s_err(
                    ty.span(),
                    "The sum of the members overflows the type size",
                ));
            };

            // clear conversion expr if not needed
            let (from, into) = match access {
                Access::ReadWrite => (from, into),
                Access::ReadOnly => (from, quote!()),
                Access::WriteOnly => (quote!(), into),
                Access::None => (quote!(), quote!()),
            };

            // compute the offset
            let offset = if order == Order::Lsb {
                offset
            } else {
                base_bits - offset - bits
            };

            // auto-conversion from zero
            if default.is_empty() {
                if !from.is_empty() {
                    default = quote!({ let this = 0u64; #from });
                } else {
                    default = quote!(0);
                }
            }

            // remove our attribute
            attrs.retain(|a| !a.path().is_ident("bits"));

            Ok(Self {
                offset,
                bits,
                base_ty,
                default,
                inner: Some(MemberInner {
                    ident,
                    ty,
                    attrs,
                    vis,
                    into,
                    from,
                }),
            })
        } else {
            if default.is_empty() {
                default = quote!(0);
            }

            Ok(Self {
                offset,
                bits,
                base_ty,
                default,
                inner: None,
            })
        }
    }

    fn debug(&self) -> TokenStream {
        if let Some(inner) = &self.inner {
            if !inner.from.is_empty() {
                let ident = &inner.ident;
                return quote!(.field(stringify!(#ident), &self.#ident()));
            }
        }
        quote!()
    }

    fn default(&self) -> TokenStream {
        let default = &self.default;

        if let Some(inner) = &self.inner {
            if !inner.into.is_empty() {
                let ident = &inner.ident;
                let with_ident = format_ident!("with_{}", ident);
                return quote!(this = this.#with_ident(#default););
            }
        }
        let offset = self.offset;
        let base_ty = &self.base_ty;
        quote!(this.0 |= (#default as #base_ty) << #offset;)
    }

    fn spec_default(&self) -> TokenStream {
        let default = &self.default;

        if let Some(inner) = &self.inner {
            if !inner.into.is_empty() {
                let ident = &inner.ident;
                let with_ident = format_ident!("with_{}", ident);
                return quote!(let this = this.#with_ident(#default););
            }
        }

        // fallback when there is no setter
        let offset = self.offset;
        let base_ty = &self.base_ty;
        let bits = self.bits as u32;
        quote! {
            let mask = #base_ty::MAX >> (#base_ty::BITS - #bits);
            let this = Self(this.0 | (((#default as #base_ty) & mask) << #offset));
        }
    }
}

impl ToTokens for Member {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let Self {
            offset,
            bits,
            base_ty,
            default: _,
            inner:
                Some(MemberInner {
                    ident,
                    ty,
                    attrs,
                    vis,
                    into,
                    from,
                }),
        } = self
        else {
            return Default::default();
        };

        let ident_str = ident.to_string().to_uppercase();
        let ident_upper = Ident::new(
            ident_str.strip_prefix("R#").unwrap_or(&ident_str),
            ident.span(),
        );

        let with_ident = format_ident!("with_{}", ident);
        let set_ident = format_ident!("set_{}", ident);
        let bits_ident = format_ident!("{}_BITS", ident_upper);
        let offset_ident = format_ident!("{}_OFFSET", ident_upper);

        let location = format!("\n\nBits: {offset}..{}", offset + bits);

        let doc: TokenStream = attrs
            .iter()
            .filter(|a| !a.path().is_ident("bits"))
            .map(ToTokens::to_token_stream)
            .collect();

        tokens.extend(quote! {
            const #bits_ident: usize = #bits;
            const #offset_ident: usize = #offset;
        });

        if !from.is_empty() {
            tokens.extend(quote! {
                #doc
                #[doc = #location]
                #vis const fn #ident(&self) -> #ty {
                    let mask = #base_ty::MAX >> (#base_ty::BITS - Self::#bits_ident as u32);
                    let this = (self.0 >> Self::#offset_ident) & mask;
                    #from
                }
            });
        }

        if !into.is_empty() {
            tokens.extend(quote! {
                #doc
                #[doc = #location]
                #[cfg_attr(debug_assertions, track_caller)]
                #vis const fn #with_ident(self, value: #ty) -> Self {
                    let this = value;
                    let value: #base_ty = #into;
                    let mask = #base_ty::MAX >> (#base_ty::BITS - Self::#bits_ident as u32);
                    #[allow(unused_comparisons)]
                    debug_assert!(value <= mask, "value out of bounds");
                    Self(self.0 & !(mask << Self::#offset_ident) | (value & mask) << Self::#offset_ident)
                }

                #doc
                #[doc = #location]
                #[cfg_attr(debug_assertions, track_caller)]
                #vis fn #set_ident(&mut self, value: #ty) {
                    *self = self.#with_ident(value);
                }
            });
        }
    }
}

impl Member {
    fn to_spec(&self, fields: Vec<Option<Ident>>, name: &Ident, externals: &Vec<syn::Type>) -> TokenStream {
        let mut tokens = TokenStream::new();
        let Self {
            offset,
            bits,
            base_ty,
            default: _,
            inner:
                Some(MemberInner {
                    ident,
                    ty,
                    attrs,
                    vis: _,
                    into,
                    from,
                }),
        } = self
        else {
            return Default::default();
        };

        let _ident_str = ident.to_string().to_uppercase();

        let reveal_ident = format_ident!("reveal_{}", ident);
        let with_ident = format_ident!("with_{}", ident);
        let lemma_with_ident = format_ident!("lemma_with_{}", ident);
        let proof_with_ident = format_ident!("proof_with_{}", ident);
        let with_ident_checked = format_ident!("with_{}_checked", ident);
        let reveal_with_ident_checked = format_ident!("reveal_with_{}_checked", ident);
        let bits_ident = format_ident!("{}_bits", ident);
        let bits_ident = quote! {#bits_ident()};
        let offset_ident = format_ident!("{}_offset", ident);
        let offset_ident = quote! {#offset_ident()};

        let _name_lower = name.to_string().to_lowercase();
        let spec_name = format_ident!("Spec{}", name);

        let location = format!("\n\nBits: {offset}..{}", offset + bits);

        let doc: TokenStream = attrs
            .iter()
            .filter(|a| !a.path().is_ident("bits"))
            .map(ToTokens::to_token_stream)
            .collect();

        tokens.extend(quote! {
            impl #spec_name {
            #[verifier(inline)]
            pub open spec fn #bits_ident -> usize {
                #bits
            }

            #[verifier(inline)]
            pub open spec fn #offset_ident -> usize {
                #offset
            }
        }
        });

        if !from.is_empty() {
            tokens.extend(quote! {
                impl #spec_name {
                #doc
                #[doc = #location]
                #[verifier(inline)]
                spec fn #reveal_ident(&self) -> #ty {
                    let mask = #base_ty::MAX >> (#base_ty::BITS - Self::#bits_ident as u32);
                    let this = (self.0 >> Self::#offset_ident) & mask;
                    #from
                }

                pub closed spec fn #ident(&self) -> #ty {
                    self.#reveal_ident()
                }
            }
            });
        }

        let other_fields: Vec<Ident>= fields.into_iter()
        .flatten() // This filters out None and unwraps Some
        .collect();

        let mut other_offset_bits = vec![];
        for f in &other_fields {
            let offset2 = format_ident!("{}_offset", f);
            let bits2 = format_ident!("{}_bits", f);
            other_offset_bits.push(quote!{
                Self::#offset2() as #base_ty, Self::#bits2() as #base_ty
            });
        }
        let reveal_other_fields: Vec<Ident>= other_fields.iter().map(|f| format_ident!("reveal_{}", f)).collect(); // This filters out None and unwraps Some
        let call_axiom_into_from = if externals.contains(&ty) {
            if let syn::Type::Path(p) = &ty {
                let axiom_into_from = format_ident!("axiom_{}_into_from_bits", p.path.get_ident().expect("external type must be a Path with ident").to_string().to_lowercase());
                quote!{#axiom_into_from(value);}
            } else {
                unreachable!()
            }
        } else {
            quote!{}
        };
        if !into.is_empty() {
            tokens.extend(quote! {
            impl #spec_name {
                #[verifier(inline)]
                spec fn #reveal_with_ident_checked(self, value: #ty) -> core::result::Result<Self, ()> {
                    let this = value;
                    let value: #base_ty = #into;
                    let mask = #base_ty::MAX >> (#base_ty::BITS - Self::#bits_ident as u32);
                    #[allow(unused_comparisons)]
                    if value > mask {
                        Err(())
                    } else {
                        let bits = self.0 & !(mask << Self::#offset_ident) | (value & mask) << Self::#offset_ident;
                        Ok(Self(bits))
                    }
                }

                pub closed spec fn #with_ident_checked(self, value: #ty) -> core::result::Result<Self, ()> {
                    self.#reveal_with_ident_checked(value)
                }

                #doc
                #[doc = #location]
                #[cfg_attr(debug_assertions, track_caller)]
                pub closed spec fn #with_ident(self, value: #ty) -> Self
                recommends self.#with_ident_checked(value).is_ok()
                {
                    self.#with_ident_checked(value).unwrap()
                }

                proof fn #lemma_with_ident(self, value: #ty) -> (ret: core::result::Result<Self, ()>)
                requires
                    self.#reveal_with_ident_checked(value).is_ok(),
                ensures
                    ::builtin::equal(ret, self.#reveal_with_ident_checked(value)),
                    ::builtin::equal((ret.unwrap()).#reveal_ident(), value),
                    #(::builtin::equal((ret.unwrap()).#reveal_other_fields(), self.#reveal_other_fields()),)*
                {
                    let ret = self.#reveal_with_ident_checked(value);
                    let ret_val = ret.unwrap();
                    if ret.is_ok() {
                    #call_axiom_into_from
                    let this = value;
                    ::verify_proof::bits::lemma_bitfield_u64_get_bits(ret_val.0, Self::#offset_ident as #base_ty, Self::#bits_ident as #base_ty);
                    ::verify_proof::bits::lemma_bitfield_u64_set_bits(self.0, #into, Self::#offset_ident as #base_ty, Self::#bits_ident as #base_ty);
                    ::verify_proof::bits::lemma_bit_u64_set_get_bits(
                        self.0, #into, Self::#offset_ident as #base_ty, Self::#bits_ident as #base_ty,
                    );
                    #(::verify_proof::bits::lemma_bit_u64_set_get_bits_unchanged(
                        self.0, #into, Self::#offset_ident as #base_ty, Self::#bits_ident as #base_ty,
                        #other_offset_bits
                    );
                    ::verify_proof::bits::lemma_bitfield_u64_get_bits(self.0, #other_offset_bits);
                    ::verify_proof::bits::lemma_bitfield_u64_get_bits(ret_val.0, #other_offset_bits);
                    ::verify_proof::bits::lemma_bit_u64_get_bits_bound(self.0, #other_offset_bits);
                    ::verify_proof::bits::lemma_bit_u64_get_bits_bound(ret_val.0, #other_offset_bits);
                    )*
                    }
                    ret
                }

                pub broadcast proof fn #proof_with_ident(self, value: #ty)
                requires
                    self.#with_ident_checked(value).is_ok(),
                ensures
                    ::builtin::equal((#[trigger]self.#with_ident(value)).#ident(), value),
                    #(::builtin::equal((#[trigger]self.#with_ident(value)).#other_fields(), self.#other_fields()),)*
                {
                    self.#lemma_with_ident(value);
                }
            }
            });
        }
        tokens
    }

    fn to_external_spec(&self, name: &Ident, _spec_name: &Ident) -> TokenStream {
        let mut tokens = TokenStream::new();
        let Self {
            offset,
            bits,
            base_ty: _,
            default: _,
            inner:
                Some(MemberInner {
                    ident,
                    ty,
                    attrs,
                    into,
                    from,
                    ..
                }),
            ..
        } = self
        else {
            return Default::default();
        };

        let ident_str = ident.to_string().to_uppercase();
        let ident_upper = Ident::new(
            ident_str.strip_prefix("R#").unwrap_or(&ident_str),
            ident.span(),
        );

        let name_lower = name.to_string().to_lowercase();
        let _spec_name = format_ident!("Spec{}", name);

        let with_ident = format_ident!("with_{}", ident);
        let with_ident_checked = format_ident!("with_{}_checked", ident);
        let set_ident = format_ident!("set_{}", ident);
        let _bits_ident = format_ident!("{}_BITS", ident_upper);
        let _offset_ident = format_ident!("{}_OFFSET", ident_upper);

        let ex_ident = format_ident!("ex_{}_{}", name_lower, ident);
        let ex_with_ident = format_ident!("ex_with_{}_{}", name_lower, ident);
        let ex_set_ident = format_ident!("ex_set_{}_{}", name_lower, ident);
        let ex_bits_ident = format_ident!("ex_{}_{}_bits", name_lower, ident_upper);
        let _ex_bits_ident = quote! {#ex_bits_ident()};
        let ex_offset_ident = format_ident!("ex_{}_{}_offset", name_lower, ident_upper);
        let _ex_offset_ident = quote! {#ex_offset_ident()};
       let _spec_from_bits = format_ident!("spec_{}_{}_from_bits", name_lower, ident);
        let _spec_into_bits = format_ident!("spec_{}_{}_into_bits", name_lower, ident);

        let location = format!("\n\nBits: {offset}..{}", offset + bits);

        let doc: TokenStream = attrs
            .iter()
            .filter(|a| !a.path().is_ident("bits"))
            .map(ToTokens::to_token_stream)
            .collect();

        tokens.extend(quote! {
            /*
            #[verifier(external_fn_specification)]
            pub fn #ex_bits_ident -> (ret: usize)
            ensures
                ret == #bits_ident()
            {
                #name::#bits_ident
            }

            #[verifier(external_fn_specification)]
            pub fn #ex_offset_ident -> (ret: usize)
            ensures
                ret == #offset_ident()
            {
                #name::#offset_ident
            }
            */
        });

        if !from.is_empty() {
            tokens.extend(quote! {
                #doc
                #[doc = #location]
                #[verifier(external_fn_specification)]
                pub fn #ex_ident(v: &#name) -> (ret: #ty)
                ensures
                    ::builtin::equal(ret, v@.#ident())
                {
                    v.#ident()
                }
            });
        }

        if !into.is_empty() {
            tokens.extend(quote! {
                #doc
                #[doc = #location]
                #[cfg_attr(debug_assertions, track_caller)]
                #[verifier(external_fn_specification)]
                pub fn #ex_with_ident(this: #name, value: #ty) -> (ret: #name)
                ensures
                    this@.#with_ident_checked(value).is_ok(),
                    builtin::equal(ret@, this@.#with_ident(value)),
                {
                    this.#with_ident(value)
                }

                #[verifier(external_fn_specification)]
                pub fn #ex_set_ident(this: &mut #name, value: #ty)
                ensures
                    old(this)@.#with_ident_checked(value).is_ok(),
                    builtin::equal(this@, old(this)@.#with_ident(value)),
                {
                    this.#set_ident(value)
                }
            });
        }
        tokens
    }
}

/// Distinguish between different types for code generation.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum TypeClass {
    /// Booleans with 1 bit size
    Bool,
    /// Unsigned ints with fixes sizes: u8, u64, ...
    UInt,
    /// Signed ints with fixes sizes: i8, i64, ...
    SInt,
    /// Custom types
    Other,
}

/// Field information, including the `bits` attribute
struct Field {
    bits: usize,
    ty: syn::Type,

    default: TokenStream,
    into: TokenStream,
    from: TokenStream,

    access: Access,
}

/// Parses the `bits` attribute that allows specifying a custom number of bits.
fn parse_field(
    base_ty: &syn::Type,
    attrs: &[syn::Attribute],
    ty: &syn::Type,
    ignore: bool,
) -> syn::Result<Field> {
    fn malformed(mut e: syn::Error, attr: &syn::Attribute) -> syn::Error {
        e.combine(s_err(attr.span(), "malformed #[bits] attribute"));
        e
    }

    let access = if ignore {
        Access::None
    } else {
        Access::ReadWrite
    };

    // Defaults for the different types
    let (class, ty_bits) = type_bits(ty);
    let mut ret = match class {
        TypeClass::Bool => Field {
            bits: ty_bits,
            ty: ty.clone(),
            default: quote!(false),
            into: quote!(this as _),
            from: quote!(this != 0),
            access,
        },
        TypeClass::SInt => Field {
            bits: ty_bits,
            ty: ty.clone(),
            default: quote!(0),
            into: quote!(),
            from: quote!(),
            access,
        },
        TypeClass::UInt => Field {
            bits: ty_bits,
            ty: ty.clone(),
            default: quote!(0),
            into: quote!(this as _),
            from: quote!(this as _),
            access,
        },
        TypeClass::Other => Field {
            bits: ty_bits,
            ty: ty.clone(),
            default: quote!(),
            into: quote!(<#ty>::into_bits(this) as _),
            from: quote!(<#ty>::from_bits(this as _)),
            access,
        },
    };

    // Find and parse the bits attribute
    for attr in attrs {
        let syn::Attribute {
            style: syn::AttrStyle::Outer,
            meta: syn::Meta::List(syn::MetaList { path, tokens, .. }),
            ..
        } = attr
        else {
            continue;
        };
        if path.is_ident("bits") {
            let span = tokens.span();
            let BitsAttr {
                bits,
                default,
                into,
                from,
                access,
            } = syn::parse2(tokens.clone()).map_err(|e| malformed(e, attr))?;

            // bit size
            if let Some(bits) = bits {
                if bits == 0 {
                    return Err(s_err(span, "bits cannot bit 0"));
                }
                if ty_bits != 0 && bits > ty_bits {
                    return Err(s_err(span, "overflowing field type"));
                }
                ret.bits = bits;
            }

            // read/write access
            if let Some(access) = access {
                if ignore {
                    return Err(s_err(
                        tokens.span(),
                        "'access' is not supported for padding",
                    ));
                }
                ret.access = access;
            }

            // conversion
            if let Some(into) = into {
                if ret.access == Access::None {
                    return Err(s_err(into.span(), "'into' is not supported on padding"));
                }
                ret.into = quote!(#into(this) as _);
            }
            if let Some(from) = from {
                if ret.access == Access::None {
                    return Err(s_err(from.span(), "'from' is not supported on padding"));
                }
                ret.from = quote!(#from(this as _));
            }
            if let Some(default) = default {
                ret.default = default.into_token_stream();
            }
        }
    }

    if ret.bits == 0 {
        return Err(s_err(
            ty.span(),
            "Custom types and isize/usize require an explicit bit size",
        ));
    }

    // Signed integers need some special handling...
    if !ignore && ret.access != Access::None && class == TypeClass::SInt {
        let bits = ret.bits as u32;
        if ret.into.is_empty() {
            // Bounds check and remove leading ones from negative values
            ret.into = quote! {{
                debug_assert!({
                    let m = #ty::MIN >> (#ty::BITS - #bits);
                    m <= this && this <= -(m + 1)
                });
                let mask = #base_ty::MAX >> (#base_ty::BITS - #bits);
                (this as #base_ty & mask)
            }};
        }
        if ret.from.is_empty() {
            // Sign extend negative values
            ret.from = quote! {{
                let shift = #ty::BITS - #bits;
                ((this as #ty) << shift) >> shift
            }};
        }
    }

    Ok(ret)
}

/// The bits attribute of the fields of a bitfield struct
struct BitsAttr {
    bits: Option<usize>,
    default: Option<syn::Expr>,
    into: Option<syn::Path>,
    from: Option<syn::Path>,
    access: Option<Access>,
}

impl Parse for BitsAttr {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let mut attr = Self {
            bits: None,
            default: None,
            into: None,
            from: None,
            access: None,
        };
        if let Ok(bits) = syn::LitInt::parse(input) {
            attr.bits = Some(bits.base10_parse()?);
            if !input.is_empty() {
                <Token![,]>::parse(input)?;
            }
        }
        // parse remainder
        if !input.is_empty() {
            loop {
                let ident = syn::Ident::parse(input)?;

                <Token![=]>::parse(input)?;

                if ident == "default" {
                    attr.default = Some(input.parse()?);
                } else if ident == "into" {
                    attr.into = Some(input.parse()?);
                } else if ident == "from" {
                    attr.from = Some(input.parse()?);
                } else if ident == "access" {
                    attr.access = Some(input.parse()?);
                }

                if input.is_empty() {
                    break;
                }

                <Token![,]>::parse(input)?;
            }
        }
        Ok(attr)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Access {
    ReadWrite,
    ReadOnly,
    WriteOnly,
    None,
}

impl Parse for Access {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let mode = input.parse::<Ident>()?;

        if mode == "RW" {
            Ok(Self::ReadWrite)
        } else if mode == "RO" {
            Ok(Self::ReadOnly)
        } else if mode == "WO" {
            Ok(Self::WriteOnly)
        } else if mode == "None" {
            Ok(Self::None)
        } else {
            Err(s_err(
                mode.span(),
                "Invalid access mode, only RW, RO, WO, or None are allowed",
            ))
        }
    }
}

#[derive(Clone, Copy, PartialEq)]
enum Order {
    Lsb,
    Msb,
}

/// The bitfield macro parameters
struct Params {
    ty: syn::Type,
    bits: usize,
    debug: bool,
    default: bool,
    order: Order,
    conversion: bool,
}

impl Parse for Params {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let Ok(ty) = syn::Type::parse(input) else {
            return Err(s_err(input.span(), "unknown type"));
        };
        let (class, bits) = type_bits(&ty);
        if class != TypeClass::UInt {
            return Err(s_err(input.span(), "unsupported type"));
        }

        let mut debug = true;
        let mut default = true;
        let mut order = Order::Lsb;
        let mut conversion = true;

        // try parse additional args
        while <Token![,]>::parse(input).is_ok() {
            let ident = Ident::parse(input)?;
            <Token![=]>::parse(input)?;
            match ident.to_string().as_str() {
                "debug" => {
                    debug = syn::LitBool::parse(input)?.value;
                }
                "default" => {
                    default = syn::LitBool::parse(input)?.value;
                }
                "order" => {
                    order = match syn::Ident::parse(input)?.to_string().as_str() {
                        "Msb" | "msb" => Order::Msb,
                        "Lsb" | "lsb" => Order::Lsb,
                        _ => return Err(s_err(ident.span(), "unknown value for order")),
                    };
                }
                "conversion" => {
                    conversion = syn::LitBool::parse(input)?.value;
                }
                _ => return Err(s_err(ident.span(), "unknown argument")),
            };
        }

        Ok(Self {
            ty,
            bits,
            debug,
            default,
            order,
            conversion,
        })
    }
}

/// The bitfield macro parameters
struct SpecParams {
    spec_only: bool,
    externals: Vec<ExternalStruct>,
}

struct ExternalStruct {
    ty: syn::Type,
    bits: usize,
}

impl Parse for ExternalStruct {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let ty = syn::Type::parse(input)?;
        let group = proc_macro2::Group::parse(input)?;
        let tokens = group.stream();
        let lit: syn::LitInt = syn::parse2(tokens)?;
        let bits: usize = lit.base10_parse::<usize>().unwrap();
        Ok(ExternalStruct {
            bits, ty
        })
    }

}

impl Parse for SpecParams {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let mut ret = SpecParams {
            spec_only: false,
            externals: vec![],
        };

        // try parse additional args
        while let Ok(ident) = Ident::parse(input) {
            <Token![=]>::parse(input)?;
            match ident.to_string().as_str() {
                "spec_only" => {
                    let b: syn::LitBool = input.parse()?;
                    ret.spec_only = b.value;
                }
                "external" => {
                    ret.externals.push(input.parse()?);
                }
                _ => return Err(s_err(ident.span(), "unknown argument")),
            };
            if <Token![,]>::parse(input).is_err() {
                break;
            }
        }

        Ok(ret)
    }
}


/// Returns the number of bits for a given type
fn type_bits(ty: &syn::Type) -> (TypeClass, usize) {
    let syn::Type::Path(syn::TypePath { path, .. }) = ty else {
        return (TypeClass::Other, 0);
    };
    let Some(ident) = path.get_ident() else {
        return (TypeClass::Other, 0);
    };
    if ident == "bool" {
        return (TypeClass::Bool, 1);
    }
    if ident == "isize" || ident == "usize" {
        return (TypeClass::UInt, 0); // they have architecture dependend sizes
    }
    macro_rules! integer {
        ($ident:ident => $($uint:ident),* ; $($sint:ident),*) => {
            match ident {
                $(_ if ident == stringify!($uint) => (TypeClass::UInt, $uint::BITS as _),)*
                $(_ if ident == stringify!($sint) => (TypeClass::SInt, $sint::BITS as _),)*
                _ => (TypeClass::Other, 0)
            }
        };
    }
    integer!(ident => u8, u16, u32, u64, u128 ; i8, i16, i32, i64, i128)
}

#[cfg(test)]
mod test {
    use quote::quote;

    use crate::{Access, BitsAttr, Order, Params};

    #[test]
    fn parse_args() {
        let args = quote!(u64);
        let params = syn::parse2::<Params>(args).unwrap();
        assert!(params.bits == u64::BITS as usize && params.debug == true);

        let args = quote!(u32, debug = false);
        let params = syn::parse2::<Params>(args).unwrap();
        assert!(params.bits == u32::BITS as usize && params.debug == false);

        let args = quote!(u32, order = Msb);
        let params = syn::parse2::<Params>(args).unwrap();
        assert!(params.bits == u32::BITS as usize && params.order == Order::Msb);
    }

    #[test]
    fn parse_bits() {
        let args = quote!(8);
        let attr = syn::parse2::<BitsAttr>(args).unwrap();
        assert_eq!(attr.bits, Some(8));
        assert!(attr.default.is_none());
        assert!(attr.into.is_none());
        assert!(attr.from.is_none());
        assert!(attr.access.is_none());

        let args = quote!(8, default = 8, access = RW);
        let attr = syn::parse2::<BitsAttr>(args).unwrap();
        assert_eq!(attr.bits, Some(8));
        assert!(attr.default.is_some());
        assert!(attr.into.is_none());
        assert!(attr.from.is_none());
        assert_eq!(attr.access, Some(Access::ReadWrite));

        let args = quote!(access = RO);
        let attr = syn::parse2::<BitsAttr>(args).unwrap();
        assert_eq!(attr.bits, None);
        assert!(attr.default.is_none());
        assert!(attr.into.is_none());
        assert!(attr.from.is_none());
        assert_eq!(attr.access, Some(Access::ReadOnly));

        let args = quote!(default = 8, access = WO);
        let attr = syn::parse2::<BitsAttr>(args).unwrap();
        assert_eq!(attr.bits, None);
        assert!(attr.default.is_some());
        assert!(attr.into.is_none());
        assert!(attr.from.is_none());
        assert_eq!(attr.access, Some(Access::WriteOnly));

        let args = quote!(
            3,
            into = into_something,
            default = 1,
            from = from_something,
            access = None
        );
        let attr = syn::parse2::<BitsAttr>(args).unwrap();
        assert_eq!(attr.bits, Some(3));
        assert!(attr.default.is_some());
        assert!(attr.into.is_some());
        assert!(attr.from.is_some());
        assert_eq!(attr.access, Some(Access::None));
    }

    #[test]
    fn parse_access_mode() {
        let args = quote!(RW);
        let mode = syn::parse2::<Access>(args).unwrap();
        assert_eq!(mode, Access::ReadWrite);

        let args = quote!(RO);
        let mode = syn::parse2::<Access>(args).unwrap();
        assert_eq!(mode, Access::ReadOnly);

        let args = quote!(WO);
        let mode = syn::parse2::<Access>(args).unwrap();
        assert_eq!(mode, Access::WriteOnly);

        let args = quote!(None);
        let mode = syn::parse2::<Access>(args).unwrap();
        assert_eq!(mode, Access::None);

        let args = quote!(garbage);
        let mode = syn::parse2::<Access>(args);
        assert!(mode.is_err());
    }
}

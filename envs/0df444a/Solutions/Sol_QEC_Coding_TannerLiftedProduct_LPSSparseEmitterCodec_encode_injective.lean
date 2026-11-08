-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec.encode_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:29:48.438547+00:00
-- url     : https://prove2.me/submissions/ad9e0ab0-613f-4ae2-973b-5f40e6d8376f

import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEncodedChecks
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterCodec
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSSparseEmitterCodec_fields_injective
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_stream_injective


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec
open QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection
namespace QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec
theorem _root_.solution:Function.Injective encode:=by
 intro rs ss h
 exact fields_injective (stream_injective h)
end QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec

-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec.fields_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:22:11.884217+00:00
-- url     : https://prove2.me/submissions/a748667d-ef2a-43ed-ac3a-d5a1616a8302

import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEncodedChecks
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterCodec
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSSparseEmitterCodec_decode_encodeFields

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec
open QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection
namespace QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec
theorem _root_.solution:Function.Injective fields:=by
 intro rs ss h
 have he:=congrArg decodeFields h
 rw [decode_encodeFields,decode_encodeFields] at he
 exact Option.some.inj he
end QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec

-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec.decodeTyped_encode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:06:03.41877+00:00
-- url     : https://prove2.me/submissions/3bf2a53d-d4eb-4323-97ec-154a667c463c

import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEncodedChecks
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterCodec
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSSparseEmitterCodec_decode_encode
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSSparseEmitterCodec_typedRows_numeric

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic FieldProjection
namespace QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec
theorem _root_.solution {n s:ℕ} (rs:List (List (Fin n×Fin s))):
 decodeTyped n s (encode (numeric n s rs))=some rs:=by
 rw [decodeTyped,decode_encode,Option.bind_some,typedRows_numeric]
end QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec

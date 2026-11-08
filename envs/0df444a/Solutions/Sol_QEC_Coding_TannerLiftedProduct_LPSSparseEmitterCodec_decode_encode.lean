-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec.decode_encode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:31:13.043165+00:00
-- url     : https://prove2.me/submissions/1171727e-d27e-444c-8f66-3b1621527d6f

import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEncodedChecks
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterCodec
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSSparseEmitterCodec_decode_encodeFields
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSSparseEmitterCodec_parseFields_stream

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic FieldProjection
namespace QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec
theorem _root_.solution (rs:List Row):decode (encode rs)=some rs:=by
 rw [decode,encode,parseFields_stream,Option.bind_some,decode_encodeFields]
end QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec

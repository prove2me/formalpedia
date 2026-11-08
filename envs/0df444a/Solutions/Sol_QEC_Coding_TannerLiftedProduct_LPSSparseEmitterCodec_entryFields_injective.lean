-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec.entryFields_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:23:40.449889+00:00
-- url     : https://prove2.me/submissions/c996362e-20d2-4a01-84bd-a9e36d61f0db

import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEncodedChecks
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterCodec
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSSparseEmitterCodec_decodeEntries_entryFields
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSSparseEmitterCodec_entryFields_length

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec
namespace QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec
theorem _root_.solution:Function.Injective entryFields:=by
 intro r s h
 have hl:=congrArg List.length h
 rw [entryFields_length,entryFields_length] at hl
 have hn:r.length=s.length:=by omega
 have he:=congrArg (fun xs=>decodeEntries r.length (xs++[])) h
 rw [decodeEntries_entryFields,hn,decodeEntries_entryFields] at he
 exact congrArg Prod.fst (Option.some.inj he)
end QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCodec

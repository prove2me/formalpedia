-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.LPSOriginalPSLLookupMachine.original_lookup_quotient_roundtrip
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:49:15.318096+00:00
-- url     : https://prove2.me/submissions/14e50235-ac3f-4645-8c6c-7b369d60e9a6

import Definitions.Def_QEC_Coding_BitTuring_UnaryFourFieldLookup
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPSLIndexMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPSLLookupMachine
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSOriginalPSLLookupMachine_representative_decode

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSOriginalPSLLookupMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalPSLLookupMachine._p2m_local_instance_eed6317f64_203
namespace QEC.Coding.TannerLiftedProduct.LPSOriginalPSLLookupMachine
theorem _root_.solution (q:ℕ) [Fact q.Prime] (A:SL(2,ZMod q)):
 quotient q (representative q ((lpsPSLEnumerationEquiv q).symm (quotient q A)))=quotient q A:=by
 rw [representative_decode,Equiv.apply_symm_apply]
end QEC.Coding.TannerLiftedProduct.LPSOriginalPSLLookupMachine

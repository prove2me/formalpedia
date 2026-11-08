-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.LPSOriginalPSLLookupMachine.original_index_roundtrip
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:48:49.861123+00:00
-- url     : https://prove2.me/submissions/ce3c502b-355f-4afb-8190-5d0743da1e5c

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
theorem _root_.solution (q:ℕ) [Fact q.Prime] (i:Fin (lpsPSLList q).length):
 LPSOriginalPSLIndexMachine.rowIndex q (representative q i) (originalReps q)=i.val:=by
 rw [originalReps,LPSOriginalPSLIndexMachine.original_source_index,representative_decode,Equiv.symm_apply_apply]
end QEC.Coding.TannerLiftedProduct.LPSOriginalPSLLookupMachine

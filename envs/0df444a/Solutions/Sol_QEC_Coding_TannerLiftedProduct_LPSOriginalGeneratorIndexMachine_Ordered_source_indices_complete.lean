-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Ordered.source_indices_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:16:13.615953+00:00
-- url     : https://prove2.me/submissions/fe65ad6a-cbce-4e23-94aa-44570fa94317

import Definitions.Def_QEC_Coding_BitTuring_UnaryRetainedFieldComputation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPSLIndexMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPSLLookupMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGeneratorMatrixListMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectivePrime
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGeneratorIndexMachine
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSGeneratorMatrixListMachine_sourceDirections_complete


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Ordered
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Ordered._p2m_local_instance_8252a2e3b6_393
namespace QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Ordered
theorem _root_.solution {p:ℕ} (a:LPSResiduePrime p) (t:LPSGeneratorIndex p):
 (result a t).val∈indices a (LPSGeneratorMatrixListMachine.sourceDirections a.degreePrime a.degreeModFour):=by
 apply List.mem_map.mpr
 exact ⟨t,LPSGeneratorMatrixListMachine.sourceDirections_complete _ _ t,rfl⟩
end QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Ordered

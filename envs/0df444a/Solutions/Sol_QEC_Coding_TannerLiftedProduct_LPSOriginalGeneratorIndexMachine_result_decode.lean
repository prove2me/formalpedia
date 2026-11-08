-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.result_decode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:45:46.224988+00:00
-- url     : https://prove2.me/submissions/32e5a37a-931c-4aee-a554-4dfe8b88cd65

import Definitions.Def_QEC_Coding_BitTuring_UnaryRetainedFieldComputation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPSLIndexMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPSLLookupMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGeneratorMatrixListMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectivePrime
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGeneratorIndexMachine
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuaternionVertexIndex_decode


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine._p2m_local_instance_8252a2e3b6_378
namespace QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine
theorem _root_.solution {p:ℕ} (a:LPSResiduePrime p) (t:LPSGeneratorIndex p):
 (lpsPSLEnumerationEquiv a.q) (result a t)=lpsQuaternionLabel a t:=
 lpsQuaternionVertexIndex_decode a t.val (norm_eq_of_mem_lpsQuaternionShell a.degreePrime.pos t.property)
end QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine

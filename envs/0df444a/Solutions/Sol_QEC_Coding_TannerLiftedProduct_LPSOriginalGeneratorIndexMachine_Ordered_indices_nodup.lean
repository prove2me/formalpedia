-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Ordered.indices_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:55:31.183175+00:00
-- url     : https://prove2.me/submissions/4402c244-775e-4037-9884-9c66a5de4b69

import Definitions.Def_QEC_Coding_BitTuring_UnaryRetainedFieldComputation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPSLIndexMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPSLLookupMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGeneratorMatrixListMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectivePrime
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGeneratorIndexMachine
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSOriginalGeneratorIndexMachine_result_injective

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Ordered
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Ordered._p2m_local_instance_8252a2e3b6_393
namespace QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Ordered
theorem _root_.solution {p:ℕ} (a:LPSResiduePrime p) (ts:List (LPSGeneratorIndex p)) (h:ts.Nodup):
 (indices a ts).Nodup:=by
 apply h.map
 intro t u he
 apply result_injective a
 exact Fin.ext he
end QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Ordered

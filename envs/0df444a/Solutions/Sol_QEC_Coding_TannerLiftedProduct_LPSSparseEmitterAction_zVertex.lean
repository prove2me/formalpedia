-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.LPSSparseEmitterAction.zVertex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:20:51.280342+00:00
-- url     : https://prove2.me/submissions/c1bf43e4-ed28-4538-8012-36d7d71de546

import Definitions.Def_QEC_Coding_BitTuring_UnarySparseEmitterArithmetic
import Definitions.Def_QEC_Coding_BitTuring_SuffixJoin
import Definitions.Def_QEC_Coding_BitTuring_UnaryRetainedFieldComputation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPSLGroupOperationsMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGeneratorVoltageMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPSLListMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterRowMachine

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSSparseEmitterAction
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSSparseEmitterAction._p2m_local_instance_8f991ae56e_149
open LPSOriginalGeneratorIndexMachine
namespace QEC.Coding.TannerLiftedProduct.LPSSparseEmitterAction
theorem _root_.solution {q:ℕ} [Fact q.Prime] (v i:LPSSparseGroupIndex q):product false true v i=lpsPSLIndexMul q i v:=rfl
end QEC.Coding.TannerLiftedProduct.LPSSparseEmitterAction

-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.LPSSparseEmitterAction.xVertex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:19:54.855479+00:00
-- url     : https://prove2.me/submissions/ff4d7502-2f4c-46be-b159-67307babb295

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
theorem _root_.solution {q:ℕ} [Fact q.Prime] (v i:LPSSparseGroupIndex q):product false false v i=lpsPSLIndexMul q v i:=rfl
end QEC.Coding.TannerLiftedProduct.LPSSparseEmitterAction

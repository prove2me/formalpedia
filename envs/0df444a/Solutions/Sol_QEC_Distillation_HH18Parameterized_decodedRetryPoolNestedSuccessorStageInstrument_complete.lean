-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolNestedSuccessorStageInstrument_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T19:57:52.586504+00:00
-- url     : https://prove2.me/submissions/bbc6b744-5d7a-4fd0-bd78-f7002c3dcaca

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_StageTransition
import Definitions.Def_QEC_Semantics_Instruments_NestedTensor_Power
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_NestedSuccessorStage
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorStageInstrument_complete
import Theorems.Thm_QEC_Semantics_FiniteInstrument_nestedTensorPower_complete


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z) :
    (decodedRetryPoolNestedSuccessorStageInstrument
      h hdegree z q stage hstage).kraus.Complete := by
  exact nestedTensorPower_complete
    (decodedRetryPoolSuccessorStageInstrument h hdegree z q stage hstage)
    (decodedRetryPoolSuccessorStageInstrument_complete h hdegree z q stage hstage)
    (logicalOutputCount m w) stage.1
end QEC.Distillation.HH18Parameterized

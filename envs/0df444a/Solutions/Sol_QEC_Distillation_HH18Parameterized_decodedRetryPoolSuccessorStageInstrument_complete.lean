-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorStageInstrument_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T19:51:07.153432+00:00
-- url     : https://prove2.me/submissions/40cf236c-5e6e-4e7f-8d22-4aae40d62895

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_StageTransition
import Definitions.Def_QEC_Semantics_Instruments_NestedTensor_Power
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_NestedSuccessorStage
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolInstrument_complete
import Theorems.Thm_QEC_Semantics_FiniteInstrument_bindDependent_complete
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPower_complete
import Theorems.Thm_QEC_Semantics_QuantumChannel_toFiniteInstrument_complete


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
    (decodedRetryPoolSuccessorStageInstrument h hdegree z q stage hstage).kraus.Complete := by
  exact FiniteInstrument.bindDependent_complete
    (QuantumChannel.toFiniteInstrument
      (decodedRetryPoolSuccessorNestedInputChannel m w z q stage hstage))
    (fun _ =>
      (decodedRetryPoolInstrument h hdegree
        (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
        (decodedRetryPoolBackwardSchedule m w z q ⟨stage.1 + 1, hstage⟩)).tensorPower
          (logicalOutputCount m w))
    (QuantumChannel.toFiniteInstrument_complete
      (decodedRetryPoolSuccessorNestedInputChannel m w z q stage hstage))
    (fun _ =>
      (decodedRetryPoolInstrument h hdegree
        (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
        (decodedRetryPoolBackwardSchedule m w z q ⟨stage.1 + 1, hstage⟩)).tensorPower_complete
          (decodedRetryPoolInstrument_complete h hdegree
            (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
            (decodedRetryPoolBackwardSchedule m w z q ⟨stage.1 + 1, hstage⟩))
          (logicalOutputCount m w))
end QEC.Distillation.HH18Parameterized

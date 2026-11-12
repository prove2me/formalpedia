-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorStageInstrument_observe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:50:05.788084+00:00
-- url     : https://prove2.me/submissions/cce5452c-343a-462d-b7a8-449699f3dd7a

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_StageTransition
import Definitions.Def_QEC_Semantics_Instruments_NestedTensor_Power
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_NestedSuccessorStage
import Theorems.Thm_QEC_Semantics_FiniteInstrument_bindDependent_observe


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
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (firstIndex : Fin
      ((decodedRetryPoolSuccessorNestedInputChannel m w z q stage hstage).chosenKrausCount))
    (secondHistory : tensorPowerHistory
      (decodedRetryPoolRawIndex h hdegree
        (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
        (decodedRetryPoolBackwardSchedule m w z q ⟨stage.1 + 1, hstage⟩))
      (logicalOutputCount m w)) :
    (decodedRetryPoolSuccessorStageInstrument h hdegree z q stage hstage).observe
        ⟨firstIndex, secondHistory⟩ =
      ⟨PUnit.unit,
        ((decodedRetryPoolInstrument h hdegree
          (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
          (decodedRetryPoolBackwardSchedule m w z q
            ⟨stage.1 + 1, hstage⟩)).tensorPower
              (logicalOutputCount m w)).observe secondHistory⟩ := by
  exact FiniteInstrument.bindDependent_observe
    (QuantumChannel.toFiniteInstrument
      (decodedRetryPoolSuccessorNestedInputChannel m w z q stage hstage))
    (fun _ =>
      (decodedRetryPoolInstrument h hdegree
        (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
        (decodedRetryPoolBackwardSchedule m w z q ⟨stage.1 + 1, hstage⟩)).tensorPower
          (logicalOutputCount m w))
    firstIndex secondHistory
end QEC.Distillation.HH18Parameterized

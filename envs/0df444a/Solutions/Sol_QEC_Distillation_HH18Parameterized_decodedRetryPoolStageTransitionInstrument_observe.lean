-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolStageTransitionInstrument_observe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:49:49.103207+00:00
-- url     : https://prove2.me/submissions/e451db93-80a0-445d-96a3-c48e192af946

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_HandoffInstrument
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_StageTransition
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
    (firstIndex : decodedRetryPoolSuccessorHandoffRawIndex
      h hdegree z q stage hstage)
    (secondHistory : decodedRetryPoolStageTransitionNextRawHistory
      h hdegree z q stage hstage) :
    (decodedRetryPoolStageTransitionInstrument h hdegree z q stage hstage).observe
        ⟨firstIndex, secondHistory⟩ =
      ⟨(decodedRetryPoolSuccessorHandoffInstrument
          h hdegree z q stage hstage).observe firstIndex,
        ((decodedRetryPoolInstrument h hdegree
          (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
          (decodedRetryPoolBackwardSchedule m w z q
            ⟨stage.1 + 1, hstage⟩)).tensorPower
              (logicalOutputCount m w)).observe secondHistory⟩ := by
  exact FiniteInstrument.bindDependent_observe
    (decodedRetryPoolSuccessorHandoffInstrument h hdegree z q stage hstage)
    (fun _ =>
      (decodedRetryPoolInstrument h hdegree
        (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
        (decodedRetryPoolBackwardSchedule m w z q ⟨stage.1 + 1, hstage⟩)).tensorPower
          (logicalOutputCount m w))
    firstIndex secondHistory
end QEC.Distillation.HH18Parameterized

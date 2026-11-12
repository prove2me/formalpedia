-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolStageTransitionInstrument_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T20:38:49.90759+00:00
-- url     : https://prove2.me/submissions/b58cc08d-3837-4046-a14a-d16ef0d0b3e5

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_HandoffInstrument
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_StageTransition
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolInstrument_complete
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorHandoffInstrument_complete
import Theorems.Thm_QEC_Semantics_FiniteInstrument_bindDependent_complete
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPower_complete


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
    (decodedRetryPoolStageTransitionInstrument h hdegree z q stage hstage).kraus.Complete := by
  exact FiniteInstrument.bindDependent_complete
    (decodedRetryPoolSuccessorHandoffInstrument h hdegree z q stage hstage)
    (fun _ =>
      (decodedRetryPoolInstrument h hdegree
        (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
        (decodedRetryPoolBackwardSchedule m w z q ⟨stage.1 + 1, hstage⟩)).tensorPower
          (logicalOutputCount m w))
    (decodedRetryPoolSuccessorHandoffInstrument_complete
      h hdegree z q stage hstage)
    (fun _ =>
      (decodedRetryPoolInstrument h hdegree
        (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
        (decodedRetryPoolBackwardSchedule m w z q
          ⟨stage.1 + 1, hstage⟩)).tensorPower_complete
            (decodedRetryPoolInstrument_complete h hdegree
              (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
              (decodedRetryPoolBackwardSchedule m w z q ⟨stage.1 + 1, hstage⟩))
            (logicalOutputCount m w))
end QEC.Distillation.HH18Parameterized

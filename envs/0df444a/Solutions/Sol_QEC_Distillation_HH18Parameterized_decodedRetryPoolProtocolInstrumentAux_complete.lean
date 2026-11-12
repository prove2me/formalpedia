-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolInstrumentAux_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T20:39:56.40413+00:00
-- url     : https://prove2.me/submissions/86012051-4ece-49c4-ab37-b4e6057ff091

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_NestedSuccessorStage
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Protocol
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolInstrument_complete
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolNestedSuccessorStageInstrument_complete
import Theorems.Thm_QEC_Semantics_FiniteInstrument_bind_complete


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
    (z q : Nat) (hz : 0 < z) : (stage : Nat) -> (hstage : stage < z) ->
    (decodedRetryPoolProtocolInstrumentAux
      h hdegree z q hz stage hstage).kraus.Complete
  | 0, hzero =>
      decodedRetryPoolInstrument_complete h hdegree
        (decodedRetryPoolBackwardAttempts m w z q ⟨0, hzero⟩)
        (decodedRetryPoolBackwardSchedule m w z q ⟨0, hzero⟩)
  | stage + 1, hstage => by
      let previousProof : stage < z := by omega
      exact FiniteInstrument.bind_complete
        (decodedRetryPoolProtocolInstrumentAux
          h hdegree z q hz stage previousProof)
        (fun _ => decodedRetryPoolProtocolSuccessorInstrumentAux
          h hdegree z q stage hstage)
        (solution
          h hdegree z q hz stage previousProof)
        (fun _ => decodedRetryPoolNestedSuccessorStageInstrument_complete
          h hdegree z q ⟨stage, previousProof⟩ hstage)
end QEC.Distillation.HH18Parameterized

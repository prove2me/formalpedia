-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorHandoffInstrument_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T19:54:22.258823+00:00
-- url     : https://prove2.me/submissions/1e2127b3-48f7-4746-b07a-eef42ce2db3c

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Regrouping
import Definitions.Def_QEC_Semantics_Channels_Instrument
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_HandoffInstrument
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolInstrument_complete
import Theorems.Thm_QEC_Semantics_FiniteInstrument_bindDependent_complete
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
    (decodedRetryPoolSuccessorHandoffInstrument h hdegree z q stage hstage).kraus.Complete := by
  change
    ((decodedRetryPoolInstrument h hdegree
        (decodedRetryPoolBackwardAttempts m w z q stage)
        (decodedRetryPoolBackwardSchedule m w z q stage)).bindDependent
      (fun _ => QuantumChannel.toFiniteInstrument
        (decodedRetryPoolSuccessorNestedInputChannel m w z q stage hstage))).kraus.Complete
  exact FiniteInstrument.bindDependent_complete
    (decodedRetryPoolInstrument h hdegree
      (decodedRetryPoolBackwardAttempts m w z q stage)
      (decodedRetryPoolBackwardSchedule m w z q stage))
    (fun _ => QuantumChannel.toFiniteInstrument
      (decodedRetryPoolSuccessorNestedInputChannel m w z q stage hstage))
    (decodedRetryPoolInstrument_complete h hdegree
      (decodedRetryPoolBackwardAttempts m w z q stage)
      (decodedRetryPoolBackwardSchedule m w z q stage))
    (fun _ => QuantumChannel.toFiniteInstrument_complete
      (decodedRetryPoolSuccessorNestedInputChannel m w z q stage hstage))
end QEC.Distillation.HH18Parameterized

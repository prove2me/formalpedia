-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorHandoffInstrument_observe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:49:30.408234+00:00
-- url     : https://prove2.me/submissions/9b659160-40ed-4692-bd88-886b79abf534

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Regrouping
import Definitions.Def_QEC_Semantics_Channels_Instrument
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_HandoffInstrument
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
    (firstIndex : decodedRetryPoolRawIndex h hdegree
      (decodedRetryPoolBackwardAttempts m w z q stage)
      (decodedRetryPoolBackwardSchedule m w z q stage))
    (secondIndex : Fin
      ((decodedRetryPoolSuccessorNestedInputChannel m w z q stage hstage).chosenKrausCount)) :
    (decodedRetryPoolSuccessorHandoffInstrument h hdegree z q stage hstage).observe
        ⟨firstIndex, secondIndex⟩ =
      ⟨(decodedRetryPoolInstrument h hdegree
          (decodedRetryPoolBackwardAttempts m w z q stage)
          (decodedRetryPoolBackwardSchedule m w z q stage)).observe firstIndex,
        PUnit.unit⟩ := by
  change
    ((decodedRetryPoolInstrument h hdegree
        (decodedRetryPoolBackwardAttempts m w z q stage)
        (decodedRetryPoolBackwardSchedule m w z q stage)).bindDependent
      (fun _ => QuantumChannel.toFiniteInstrument
        (decodedRetryPoolSuccessorNestedInputChannel m w z q stage hstage))).observe
      ⟨firstIndex, secondIndex⟩ = _
  exact FiniteInstrument.bindDependent_observe
    (decodedRetryPoolInstrument h hdegree
      (decodedRetryPoolBackwardAttempts m w z q stage)
      (decodedRetryPoolBackwardSchedule m w z q stage))
    (fun _ => QuantumChannel.toFiniteInstrument
      (decodedRetryPoolSuccessorNestedInputChannel m w z q stage hstage))
    firstIndex secondIndex
end QEC.Distillation.HH18Parameterized

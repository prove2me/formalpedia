-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolInstrumentAux_observe_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:51:20.834203+00:00
-- url     : https://prove2.me/submissions/2bd5cfeb-7633-4aab-8e2a-34a0afd50fb6

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_NestedSuccessorStage
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Protocol

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
    (z q : Nat) (hz : 0 < z) (stage : Nat) (hstage : stage + 1 < z)
    (firstIndex : decodedRetryPoolProtocolRawIndexAux
      h hdegree z q stage (by omega))
    (secondIndex : nestedTensorHistory
      (decodedRetryPoolSuccessorStageRawIndex
        h hdegree z q ⟨stage, by omega⟩ hstage)
      (logicalOutputCount m w) stage) :
    (decodedRetryPoolProtocolInstrumentAux
      h hdegree z q hz (stage + 1) hstage).observe
        (firstIndex, secondIndex) =
      ⟨(decodedRetryPoolProtocolInstrumentAux
          h hdegree z q hz stage (by omega)).observe firstIndex,
        (decodedRetryPoolProtocolSuccessorInstrumentAux
          h hdegree z q stage hstage).observe secondIndex⟩ := by
  rfl
end QEC.Distillation.HH18Parameterized

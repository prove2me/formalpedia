-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolInstrumentAux_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T19:57:22.065398+00:00
-- url     : https://prove2.me/submissions/cba7f044-7e11-482c-8ba4-9c6518867463

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
    (z q : Nat) (hz : 0 < z) (stage : Nat) (hstage : stage + 1 < z) :
    decodedRetryPoolProtocolInstrumentAux
        h hdegree z q hz (stage + 1) hstage =
      (decodedRetryPoolProtocolInstrumentAux
        h hdegree z q hz stage (by omega)).bind
        (fun _ => decodedRetryPoolProtocolSuccessorInstrumentAux
          h hdegree z q stage hstage) := by
  rfl
end QEC.Distillation.HH18Parameterized

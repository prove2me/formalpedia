-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalProtocolInstrument_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T20:48:44.403194+00:00
-- url     : https://prove2.me/submissions/70f10cf6-1c22-4531-909a-183e1106d5cd

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_NestedSuccessorStage
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Protocol
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolProtocolInstrumentToStage_complete

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
    (z q : Nat) (hz : 0 < z) :
    (decodedRetryPoolPhysicalProtocolInstrument
      h hdegree z q hz).kraus.Complete :=
  decodedRetryPoolProtocolInstrumentToStage_complete h hdegree z q hz
    (decodedRetryPoolProtocolTerminalStage z hz)
end QEC.Distillation.HH18Parameterized

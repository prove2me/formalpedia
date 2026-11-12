-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalProtocol_terminal_required
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T19:57:34.117106+00:00
-- url     : https://prove2.me/submissions/f56ac294-0717-4a59-ad3f-3ab8fb28bbff

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_NestedSuccessorStage
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Protocol
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolBackwardSchedule_terminal


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
theorem _root_.solution
    (m w z q : Nat) (hz : 0 < z) :
    decodedRetryPoolBackwardSchedule m w z q
      (decodedRetryPoolProtocolTerminalStage z hz) = q :=
  decodedRetryPoolBackwardSchedule_terminal m w z q hz
end QEC.Distillation.HH18Parameterized

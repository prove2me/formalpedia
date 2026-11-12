-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorNextTrialInput_ne_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:45:21.593198+00:00
-- url     : https://prove2.me/submissions/d883db06-8a2d-43bb-9523-80ba651e2560

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_BackwardSchedule
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Routing
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorNextTrialInput_injective

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w)
    {left right : Fin (decodedRetryPoolBackwardSchedule m w z q stage)}
    (hne : left ≠ right) :
    decodedRetryPoolSuccessorNextTrialInput m w z q stage hstage port left ≠
      decodedRetryPoolSuccessorNextTrialInput m w z q stage hstage port right := by
  intro hroute
  exact hne (decodedRetryPoolSuccessorNextTrialInput_injective
    m w z q stage hstage port hroute)
end QEC.Distillation.HH18Parameterized

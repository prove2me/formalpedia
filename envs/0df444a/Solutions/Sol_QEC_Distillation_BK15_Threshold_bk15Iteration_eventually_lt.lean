-- Prove2me | solution 1 for QEC.Distillation.BK15.Threshold.bk15Iteration_eventually_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T04:39:01.066381+00:00
-- url     : https://prove2.me/submissions/b7333227-eb49-40e6-8367-ca7447268211

import Definitions.Def_QEC_Distillation_FifteenQubitH_Recurrence
import Definitions.Def_QEC_Distillation_FifteenQubitH_Threshold
import Theorems.Thm_QEC_Distillation_BK15_Threshold_bk15Iteration_tendsto_zero

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK15
open QEC.Distillation.BK15.Threshold
open Semantics Semantics.Qubit
open NoisyInput Protocol Recurrence
open OneQubitMagic
namespace QEC.Distillation.BK15.Threshold
theorem _root_.solution
    (epsilon target : Real) (hpositive : 0 < epsilon)
    (hthreshold : epsilon < epsilonStar) (htarget : 0 < target) :
    ∃ rounds : Nat, bk15Iteration epsilon rounds < target := by
  have htendsto := bk15Iteration_tendsto_zero epsilon hpositive hthreshold
  exact ((tendsto_order.mp htendsto).2 target htarget).exists
end QEC.Distillation.BK15.Threshold

-- Prove2me | solution 1 for QEC.Distillation.BK15.Threshold.bk15Iteration_antitone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T04:25:59.107947+00:00
-- url     : https://prove2.me/submissions/f666e34f-1d37-45b4-a127-31d06c622755

import Definitions.Def_QEC_Distillation_FifteenQubitH_Recurrence
import Definitions.Def_QEC_Distillation_FifteenQubitH_Threshold

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
    (epsilon : Real) (hpositive : 0 < epsilon)
    (hthreshold : epsilon < epsilonStar) :
    Antitone (bk15Iteration epsilon) := by
  apply antitone_nat_of_succ_le
  intro rounds
  rw [bk15Iteration_succ]
  exact (bk15Recurrence_lt_input
    (bk15Iteration_pos_and_lt_epsilonStar epsilon hpositive hthreshold rounds).1
    (bk15Iteration_pos_and_lt_epsilonStar epsilon hpositive hthreshold rounds).2).le
end QEC.Distillation.BK15.Threshold

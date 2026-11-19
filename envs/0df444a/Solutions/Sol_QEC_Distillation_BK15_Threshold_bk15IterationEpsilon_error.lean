-- Prove2me | solution 1 for QEC.Distillation.BK15.Threshold.bk15IterationEpsilon_error
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T04:25:12.887353+00:00
-- url     : https://prove2.me/submissions/0a977b01-99c9-43f0-af2d-3349eef04590

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
    (hthreshold : epsilon < epsilonStar) (rounds : Nat) :
    (bk15IterationEpsilon epsilon hpositive hthreshold rounds).epsilon =
      bk15Iteration epsilon rounds := rfl
end QEC.Distillation.BK15.Threshold

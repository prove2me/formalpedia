-- Prove2me | solution 1 for QEC.Distillation.BK15.Threshold.bk15Iteration_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T04:26:55.333242+00:00
-- url     : https://prove2.me/submissions/01d5e984-e071-465c-ac12-cd98b4802075

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
theorem _root_.solution (epsilon : Real) :
    bk15Iteration epsilon 0 = epsilon := rfl
end QEC.Distillation.BK15.Threshold

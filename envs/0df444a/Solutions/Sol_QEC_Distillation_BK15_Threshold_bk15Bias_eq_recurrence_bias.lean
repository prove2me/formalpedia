-- Prove2me | solution 1 for QEC.Distillation.BK15.Threshold.bk15Bias_eq_recurrence_bias
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T04:30:49.496054+00:00
-- url     : https://prove2.me/submissions/63e7fb32-757b-4cd0-ba04-9de42bc05662

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
theorem _root_.solution (epsilon : BK15Epsilon) :
    bk15Bias epsilon.epsilon = bk15_r epsilon := by
  rfl
end QEC.Distillation.BK15.Threshold

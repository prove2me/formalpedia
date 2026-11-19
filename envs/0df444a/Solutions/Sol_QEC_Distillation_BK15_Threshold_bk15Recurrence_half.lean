-- Prove2me | solution 1 for QEC.Distillation.BK15.Threshold.bk15Recurrence_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T04:28:28.695029+00:00
-- url     : https://prove2.me/submissions/169f12a4-c60c-45ca-9c75-5c2c30e31f0f

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
theorem _root_.solution : bk15Recurrence (1 / 2) = 1 / 2 := by
  norm_num [bk15Recurrence, bk15Bias]
end QEC.Distillation.BK15.Threshold

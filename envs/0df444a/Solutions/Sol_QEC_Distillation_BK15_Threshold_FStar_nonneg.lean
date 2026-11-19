-- Prove2me | solution 1 for QEC.Distillation.BK15.Threshold.FStar_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T04:26:09.883517+00:00
-- url     : https://prove2.me/submissions/8ea4f046-5d76-42dd-aaed-595ba990cce4

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
theorem _root_.solution : 0 <= FStar := by
  exact Real.sqrt_nonneg _
end QEC.Distillation.BK15.Threshold

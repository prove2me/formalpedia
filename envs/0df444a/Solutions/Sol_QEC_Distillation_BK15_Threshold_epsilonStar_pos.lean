-- Prove2me | solution 1 for QEC.Distillation.BK15.Threshold.epsilonStar_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T04:25:31.789585+00:00
-- url     : https://prove2.me/submissions/8700428a-c6d6-4d3f-8c4b-c0aab6cd39ce

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
theorem _root_.solution : 0 < epsilonStar := by
  unfold epsilonStar
  linarith [bk15BiasStar_lt_one]
end QEC.Distillation.BK15.Threshold

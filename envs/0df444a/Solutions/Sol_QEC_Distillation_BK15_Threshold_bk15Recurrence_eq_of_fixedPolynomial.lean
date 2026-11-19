-- Prove2me | solution 1 for QEC.Distillation.BK15.Threshold.bk15Recurrence_eq_of_fixedPolynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T04:28:45.533601+00:00
-- url     : https://prove2.me/submissions/884b12ca-9de5-46f2-ae73-beb38d2b9204

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
    {epsilon : Real} (hroot : bk15FixedPolynomial (bk15Bias epsilon) = 0) :
    bk15Recurrence epsilon = epsilon := by
  have hsub := bk15Recurrence_sub_input epsilon
  rw [hroot] at hsub
  norm_num at hsub
  linarith
end QEC.Distillation.BK15.Threshold

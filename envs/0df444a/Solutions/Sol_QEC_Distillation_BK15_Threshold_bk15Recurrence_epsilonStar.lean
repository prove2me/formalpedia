-- Prove2me | solution 1 for QEC.Distillation.BK15.Threshold.bk15Recurrence_epsilonStar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T04:31:26.621133+00:00
-- url     : https://prove2.me/submissions/cd27fa84-cec7-4534-a6a6-30e1f3c1fc0e

import Definitions.Def_QEC_Distillation_FifteenQubitH_Recurrence
import Definitions.Def_QEC_Distillation_FifteenQubitH_Threshold
import Theorems.Thm_QEC_Distillation_BK15_Threshold_bk15Recurrence_eq_of_fixedPolynomial

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
theorem _root_.solution :
    bk15Recurrence epsilonStar = epsilonStar := by
  apply bk15Recurrence_eq_of_fixedPolynomial
  rw [bk15Bias_epsilonStar]
  exact bk15FixedPolynomial_biasStar
end QEC.Distillation.BK15.Threshold

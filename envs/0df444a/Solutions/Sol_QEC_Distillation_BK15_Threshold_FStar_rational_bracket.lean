-- Prove2me | solution 1 for QEC.Distillation.BK15.Threshold.FStar_rational_bracket
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T04:31:30.095755+00:00
-- url     : https://prove2.me/submissions/f832740e-3a29-4526-b2c4-93883e5e8599

import Definitions.Def_QEC_Distillation_FifteenQubitH_Recurrence
import Definitions.Def_QEC_Distillation_FifteenQubitH_Threshold
import Theorems.Thm_QEC_Distillation_BK15_Threshold_epsilonStar_rational_bracket
import Theorems.Thm_QEC_Distillation_BK15_Threshold_FStar_sq
import Theorems.Thm_QEC_Distillation_BK15_Threshold_FStar_nonneg

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
    463 / 500 < FStar ∧ FStar < 927 / 1000 := by
  constructor
  · have hsquare : (463 / 500 : Real) ^ 2 < 1 - epsilonStar := by
      linarith [epsilonStar_rational_bracket.2]
    nlinarith [FStar_sq, FStar_nonneg]
  · have hsquare : 1 - epsilonStar < (927 / 1000 : Real) ^ 2 := by
      linarith [epsilonStar_rational_bracket.1]
    nlinarith [FStar_sq, FStar_nonneg]
end QEC.Distillation.BK15.Threshold

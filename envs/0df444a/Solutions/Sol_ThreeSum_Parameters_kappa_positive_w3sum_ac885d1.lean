-- Prove2me | solution 1 for ThreeSum.Parameters.kappa_positive_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:07:13.726777+00:00
-- url     : https://prove2.me/submissions/296a9410-ec27-4717-8498-21e825a82001

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_Parameters
import Theorems.Thm_ThreeSum_Parameters_log_two_pos
import Theorems.Thm_ThreeSum_Parameters_kappa_formula

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.Parameters
open Set Real
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
namespace ThreeSum.Parameters
theorem _root_.solution : 0 < kappa := by
  have hp := (abs_le.mp (Real.sum_range_sub_log_div_le
    (by norm_num : |(1 / 1023 : ℝ)| < 1) 1)).1
  have hm := (abs_le.mp (Real.sum_range_sub_log_div_le
    (by norm_num : |(-(1 / 1021) : ℝ)| < 1) 1)).1
  norm_num [Finset.sum_range_succ] at hp hm
  have hnum : (1 / 1023 : ℝ) ≤ kappa * Real.log 2 := by
    rw [kappa_formula]
    linarith
  by_contra h
  have hnonpos := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) log_two_pos.le
  linarith
end ThreeSum.Parameters

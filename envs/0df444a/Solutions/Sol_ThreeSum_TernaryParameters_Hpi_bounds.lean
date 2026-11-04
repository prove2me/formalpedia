-- Prove2me | solution 1 for ThreeSum.TernaryParameters.Hpi_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:54:15.434227+00:00
-- url     : https://prove2.me/submissions/07fbae55-ea7b-418c-bd7e-4b1a1da2543e

import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_TernaryParameters
import Theorems.Thm_ThreeSum_TernaryParameters_log_two_pos
import Theorems.Thm_ThreeSum_TernaryParameters_log_pi0_bounds
import Theorems.Thm_ThreeSum_TernaryParameters_log_pi1_bounds
import Theorems.Thm_ThreeSum_TernaryParameters_log_pi2_bounds
import Theorems.Thm_ThreeSum_Parameters_log_two_pos

noncomputable section
namespace ThreeSum.TernaryParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
private theorem log_two_bounds :
    (13862943611198906187 / 20000000000000000000 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ (17328679513998632737 / 25000000000000000000 : ℝ) := by
  have h := Real.sum_range_sub_log_div_le
    (by norm_num : |((1 / 3 : ℝ) : ℝ)| < 1) 20
  have hratio : ((1 + (1 / 3 : ℝ)) / (1 - (1 / 3 : ℝ)) : ℝ) = 2 := by
    norm_num []
  rw [hratio] at h
  norm_num [Finset.sum_range_succ] at h
  have hh := abs_le.mp h
  constructor <;> linarith [hh.1, hh.2]
end ThreeSum.TernaryParameters
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
namespace ThreeSum.TernaryParameters
theorem _root_.solution : (1629281449055122917 / 2000000000000000000 : ℝ) ≤ Hpi ∧ Hpi ≤ (814640724527561459 / 1000000000000000000 : ℝ) := by
  have h_pi0 := log_pi0_bounds
  have h_pi1 := log_pi1_bounds
  have h_pi2 := log_pi2_bounds
  have h_two := log_two_bounds
  constructor
  · unfold Hpi
    apply (le_div_iff₀ log_two_pos).2
    norm_num [Hpi, mean, deficit, pi0, pi1, pi2, alpha0, alpha1, alpha2] at *
    linarith [h_pi0.1, h_pi0.2, h_pi1.1, h_pi1.2, h_pi2.1, h_pi2.2, h_two.1, h_two.2]
  · unfold Hpi
    apply (div_le_iff₀ log_two_pos).2
    norm_num [Hpi, mean, deficit, pi0, pi1, pi2, alpha0, alpha1, alpha2] at *
    linarith [h_pi0.1, h_pi0.2, h_pi1.1, h_pi1.2, h_pi2.1, h_pi2.2, h_two.1, h_two.2]
end ThreeSum.TernaryParameters

-- Prove2me | solution 1 for ThreeSum.TernaryParameters.Halpha_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:55:03.999163+00:00
-- url     : https://prove2.me/submissions/a318d084-236b-4228-bd6a-1fa465b6cb4d

import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_TernaryParameters
import Theorems.Thm_ThreeSum_TernaryParameters_log_two_pos
import Theorems.Thm_ThreeSum_TernaryParameters_log_alpha0_bounds
import Theorems.Thm_ThreeSum_TernaryParameters_log_alpha1_bounds
import Theorems.Thm_ThreeSum_TernaryParameters_log_alpha2_bounds
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
theorem _root_.solution : (5114333534032641009 / 10000000000000000000 : ℝ) ≤ Halpha ∧ Halpha ≤ (2557166767016320507 / 5000000000000000000 : ℝ) := by
  have h_alpha0 := log_alpha0_bounds
  have h_alpha1 := log_alpha1_bounds
  have h_alpha2 := log_alpha2_bounds
  have h_two := log_two_bounds
  constructor
  · unfold Halpha
    apply (le_div_iff₀ log_two_pos).2
    norm_num [Halpha, mean, deficit, pi0, pi1, pi2, alpha0, alpha1, alpha2] at *
    linarith [h_alpha0.1, h_alpha0.2, h_alpha1.1, h_alpha1.2, h_alpha2.1, h_alpha2.2, h_two.1, h_two.2]
  · unfold Halpha
    apply (div_le_iff₀ log_two_pos).2
    norm_num [Halpha, mean, deficit, pi0, pi1, pi2, alpha0, alpha1, alpha2] at *
    linarith [h_alpha0.1, h_alpha0.2, h_alpha1.1, h_alpha1.2, h_alpha2.1, h_alpha2.2, h_two.1, h_two.2]
end ThreeSum.TernaryParameters

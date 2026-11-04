-- Prove2me | solution 1 for ThreeSum.TernaryParameters.partitionEntropy_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:55:50.807339+00:00
-- url     : https://prove2.me/submissions/9ba7d3e0-fb6f-4af7-a755-7293f7ec8601

import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_TernaryParameters
import Theorems.Thm_ThreeSum_TernaryParameters_log_two_pos
import Theorems.Thm_ThreeSum_TernaryParameters_log_three_bounds
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
theorem _root_.solution : (512800107174161301 / 2500000000000000000 : ℝ) ≤ partitionEntropy ∧ partitionEntropy ≤ (410240085739329041 / 2000000000000000000 : ℝ) := by
  have h_three := log_three_bounds
  have h_two := log_two_bounds
  constructor
  · unfold partitionEntropy
    apply (le_div_iff₀ log_two_pos).2
    norm_num [partitionEntropy, mean, deficit, pi0, pi1, pi2, alpha0, alpha1, alpha2] at *
    linarith [h_three.1, h_three.2, h_two.1, h_two.2]
  · unfold partitionEntropy
    apply (div_le_iff₀ log_two_pos).2
    norm_num [partitionEntropy, mean, deficit, pi0, pi1, pi2, alpha0, alpha1, alpha2] at *
    linarith [h_three.1, h_three.2, h_two.1, h_two.2]
end ThreeSum.TernaryParameters

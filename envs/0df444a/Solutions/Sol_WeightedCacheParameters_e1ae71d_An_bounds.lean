-- Prove2me | solution 1 for WeightedCacheParameters_e1ae71d.An_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:08:27.937973+00:00
-- url     : https://prove2.me/submissions/e163fce3-a3a7-442a-a793-15c7da1ade17

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Definitions.Def_Submission_Weighted_Parameters_w3sum_e1ae71d
import Theorems.Thm_WeightedCacheParameters_e1ae71d_log_alpha0_bounds
import Theorems.Thm_WeightedCacheParameters_e1ae71d_log_alpha1_bounds
import Theorems.Thm_WeightedCacheParameters_e1ae71d_log_alpha2_bounds

set_option autoImplicit false
noncomputable section
open WeightedCacheParameters_e1ae71d
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 4096
namespace WeightedCacheParameters_e1ae71d
theorem _root_.solution : (5537922463388799 / 15625000000000000 : ℝ) ≤ An ∧ An ≤ (354427037656883141 / 1000000000000000000 : ℝ) := by
  have halpha0 := log_alpha0_bounds
  have halpha1 := log_alpha1_bounds
  have halpha2 := log_alpha2_bounds
  norm_num [An, pi0, pi1, pi2, alpha0, alpha1, alpha2, cutSlope, dropSlope] at *
  constructor <;> linarith
end WeightedCacheParameters_e1ae71d

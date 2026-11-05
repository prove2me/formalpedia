-- Prove2me | solution 1 for WeightedCacheParameters_e1ae71d.Hn_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:08:02.497161+00:00
-- url     : https://prove2.me/submissions/4b84b275-2a89-452c-8379-044d2a056bce

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Definitions.Def_Submission_Weighted_Parameters_w3sum_e1ae71d
import Theorems.Thm_WeightedCacheParameters_e1ae71d_log_pi0_bounds
import Theorems.Thm_WeightedCacheParameters_e1ae71d_log_pi1_bounds
import Theorems.Thm_WeightedCacheParameters_e1ae71d_log_pi2_bounds

set_option autoImplicit false
noncomputable section
open WeightedCacheParameters_e1ae71d
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 4096
namespace WeightedCacheParameters_e1ae71d
theorem _root_.solution : (141139799958643803 / 250000000000000000 : ℝ) ≤ Hn ∧ Hn ≤ (564559199834575217 / 1000000000000000000 : ℝ) := by
  have hpi0 := log_pi0_bounds
  have hpi1 := log_pi1_bounds
  have hpi2 := log_pi2_bounds
  norm_num [Hn, pi0, pi1, pi2, alpha0, alpha1, alpha2, cutSlope, dropSlope] at *
  constructor <;> linarith
end WeightedCacheParameters_e1ae71d

-- Prove2me | solution 1 for WeightedCacheParameters.Hn_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:05:11.287213+00:00
-- url     : https://prove2.me/submissions/3a0e3b04-2792-490e-92d4-57a664b3e68f

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Definitions.Def_Submission_Weighted_Parameters
import Theorems.Thm_WeightedCacheParameters_log_pi0_bounds
import Theorems.Thm_WeightedCacheParameters_log_pi1_bounds
import Theorems.Thm_WeightedCacheParameters_log_pi2_bounds

set_option autoImplicit false
noncomputable section
open WeightedCacheParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
namespace WeightedCacheParameters
theorem _root_.solution : (28226206487160407 / 50000000000000000 : ℝ) ≤ Hn ∧ Hn ≤ (35282758108950509 / 62500000000000000 : ℝ) := by
  have hpi0 := log_pi0_bounds
  have hpi1 := log_pi1_bounds
  have hpi2 := log_pi2_bounds
  norm_num [Hn, pi0, pi1, pi2, alpha0, alpha1, alpha2, cutSlope, dropSlope] at *
  constructor <;> linarith
end WeightedCacheParameters

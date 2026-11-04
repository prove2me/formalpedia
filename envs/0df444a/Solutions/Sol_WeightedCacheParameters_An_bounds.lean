-- Prove2me | solution 1 for WeightedCacheParameters.An_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:05:12.460525+00:00
-- url     : https://prove2.me/submissions/94c09b13-98c1-442e-af78-ead5349809f9

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Definitions.Def_Submission_Weighted_Parameters
import Theorems.Thm_WeightedCacheParameters_log_alpha0_bounds
import Theorems.Thm_WeightedCacheParameters_log_alpha1_bounds
import Theorems.Thm_WeightedCacheParameters_log_alpha2_bounds

set_option autoImplicit false
noncomputable section
open WeightedCacheParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
namespace WeightedCacheParameters
theorem _root_.solution : (88600888805278793 / 250000000000000000 : ℝ) ≤ An ∧ An ≤ (354403555221115177 / 1000000000000000000 : ℝ) := by
  have halpha0 := log_alpha0_bounds
  have halpha1 := log_alpha1_bounds
  have halpha2 := log_alpha2_bounds
  norm_num [An, pi0, pi1, pi2, alpha0, alpha1, alpha2, cutSlope, dropSlope] at *
  constructor <;> linarith
end WeightedCacheParameters

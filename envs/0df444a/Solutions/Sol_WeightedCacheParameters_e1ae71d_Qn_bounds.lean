-- Prove2me | solution 1 for WeightedCacheParameters_e1ae71d.Qn_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:09:38.88393+00:00
-- url     : https://prove2.me/submissions/f9c185d8-41f7-48e9-921a-3ea4deea2b06

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Definitions.Def_Submission_Weighted_Parameters_w3sum_e1ae71d
import Theorems.Thm_WeightedCacheParameters_e1ae71d_log_zRoot_bounds
import Theorems.Thm_WeightedCacheParameters_e1ae71d_log_queryArg1_bounds
import Theorems.Thm_WeightedCacheParameters_e1ae71d_log_queryArg2_bounds

set_option autoImplicit false
noncomputable section
open WeightedCacheParameters_e1ae71d
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 4096
namespace WeightedCacheParameters_e1ae71d
theorem _root_.solution : (3035725394303803 / 62500000000000000 : ℝ) ≤ Qn ∧ Qn ≤ (6071450788607613 / 125000000000000000 : ℝ) := by
  have hqueryArg1 := log_queryArg1_bounds
  have hqueryArg2 := log_queryArg2_bounds
  have hzRoot := log_zRoot_bounds
  norm_num [Qn, pi0, pi1, pi2, alpha0, alpha1, alpha2, cutSlope, dropSlope] at *
  constructor <;> linarith
end WeightedCacheParameters_e1ae71d

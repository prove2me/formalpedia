-- Prove2me | solution 1 for WeightedCacheParameters_e1ae71d.Bn_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:09:19.628064+00:00
-- url     : https://prove2.me/submissions/73ee62c8-eee3-4d18-89be-a97c8dfc1050

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Definitions.Def_Submission_Weighted_Parameters_w3sum_e1ae71d
import Theorems.Thm_WeightedCacheParameters_e1ae71d_log_yRoot_bounds
import Theorems.Thm_WeightedCacheParameters_e1ae71d_log_bankArg_bounds

set_option autoImplicit false
noncomputable section
open WeightedCacheParameters_e1ae71d
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 4096
namespace WeightedCacheParameters_e1ae71d
theorem _root_.solution : (542055703071795107 / 1000000000000000000 : ℝ) ≤ Bn ∧ Bn ≤ (542055703071795947 / 1000000000000000000 : ℝ) := by
  have hbankArg := log_bankArg_bounds
  have hyRoot := log_yRoot_bounds
  norm_num [Bn, pi0, pi1, pi2, alpha0, alpha1, alpha2, cutSlope, dropSlope] at *
  constructor <;> linarith
end WeightedCacheParameters_e1ae71d

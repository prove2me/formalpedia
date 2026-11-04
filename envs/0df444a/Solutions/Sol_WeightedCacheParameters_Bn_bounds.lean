-- Prove2me | solution 1 for WeightedCacheParameters.Bn_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:10:45.618561+00:00
-- url     : https://prove2.me/submissions/1d4f4edc-fa16-4c72-93f9-7e629cb82ee7

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Definitions.Def_Submission_Weighted_Parameters
import Theorems.Thm_WeightedCacheParameters_log_yRoot_bounds
import Theorems.Thm_WeightedCacheParameters_log_bankArg_bounds

set_option autoImplicit false
noncomputable section
open WeightedCacheParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
namespace WeightedCacheParameters
theorem _root_.solution : (542022031540465943 / 1000000000000000000 : ℝ) ≤ Bn ∧ Bn ≤ (135505507885116591 / 250000000000000000 : ℝ) := by
  have hbankArg := log_bankArg_bounds
  have hyRoot := log_yRoot_bounds
  norm_num [Bn, pi0, pi1, pi2, alpha0, alpha1, alpha2, cutSlope, dropSlope] at *
  constructor <;> linarith
end WeightedCacheParameters

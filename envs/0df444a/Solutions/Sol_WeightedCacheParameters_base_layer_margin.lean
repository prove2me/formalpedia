-- Prove2me | solution 1 for WeightedCacheParameters.base_layer_margin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:38:12.562562+00:00
-- url     : https://prove2.me/submissions/c72fc2fc-4fef-4803-86cb-5d6faead5d13

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Definitions.Def_Submission_Weighted_Parameters

set_option autoImplicit false
noncomputable section
open WeightedCacheParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
namespace WeightedCacheParameters
theorem _root_.solution : 1025 * (alpha1 + 2 * alpha2) < 2 * cutSlope := by
  norm_num [alpha1, alpha2, cutSlope]
end WeightedCacheParameters

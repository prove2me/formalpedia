-- Prove2me | solution 1 for WeightedCacheParameters_e1ae71d.base_layer_margin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:06:58.350263+00:00
-- url     : https://prove2.me/submissions/01eeb029-e618-4aa9-8d28-2e0f0c10e543

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Definitions.Def_Submission_Weighted_Parameters_w3sum_e1ae71d

set_option autoImplicit false
noncomputable section
open WeightedCacheParameters_e1ae71d
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 4096
namespace WeightedCacheParameters_e1ae71d
theorem _root_.solution : 2740 * (alpha1 + 2 * alpha2) < 2 * cutSlope := by
  norm_num [alpha1, alpha2, cutSlope]
end WeightedCacheParameters_e1ae71d

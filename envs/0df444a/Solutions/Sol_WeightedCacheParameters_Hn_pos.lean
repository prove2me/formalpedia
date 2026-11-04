-- Prove2me | solution 1 for WeightedCacheParameters.Hn_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:08:47.710962+00:00
-- url     : https://prove2.me/submissions/f1368631-f7cf-4669-b787-a622bc58d3d3

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Definitions.Def_Submission_Weighted_Parameters
import Theorems.Thm_WeightedCacheParameters_Hn_bounds

set_option autoImplicit false
noncomputable section
open WeightedCacheParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
namespace WeightedCacheParameters
theorem _root_.solution : 0 < Hn := by linarith [Hn_bounds.1]
end WeightedCacheParameters

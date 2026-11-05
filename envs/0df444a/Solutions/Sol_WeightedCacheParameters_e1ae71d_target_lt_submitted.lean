-- Prove2me | solution 1 for WeightedCacheParameters_e1ae71d.target_lt_submitted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:06:59.069973+00:00
-- url     : https://prove2.me/submissions/6a784f9a-4530-40d2-9286-ad48271002b8

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
theorem _root_.solution : targetExponent < (96013971 / 50000000 : ℝ) := by norm_num [targetExponent]
end WeightedCacheParameters_e1ae71d

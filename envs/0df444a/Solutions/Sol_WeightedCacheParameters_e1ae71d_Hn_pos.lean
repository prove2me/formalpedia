-- Prove2me | solution 1 for WeightedCacheParameters_e1ae71d.Hn_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:09:20.278205+00:00
-- url     : https://prove2.me/submissions/5d1f8ee2-fa66-487b-a6e2-a12295533a84

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Definitions.Def_Submission_Weighted_Parameters_w3sum_e1ae71d
import Theorems.Thm_WeightedCacheParameters_e1ae71d_Hn_bounds

set_option autoImplicit false
noncomputable section
open WeightedCacheParameters_e1ae71d
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 4096
namespace WeightedCacheParameters_e1ae71d
theorem _root_.solution : 0 < Hn := by linarith [Hn_bounds.1]
end WeightedCacheParameters_e1ae71d

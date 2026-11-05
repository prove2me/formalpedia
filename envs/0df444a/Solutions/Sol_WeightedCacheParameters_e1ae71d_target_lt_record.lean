-- Prove2me | solution 1 for WeightedCacheParameters_e1ae71d.target_lt_record
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T07:21:39.440801+00:00
-- url     : https://prove2.me/submissions/c37ca64e-f4ea-4dcf-8585-4bcaf5328cb3

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
theorem _root_.solution : targetExponent <
    (4800698571997281331 / 2500000000000000000 : ℝ) := by norm_num [targetExponent]
end WeightedCacheParameters_e1ae71d

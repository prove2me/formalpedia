-- Prove2me | solution 1 for WeightedCacheParameters.pi_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:38:09.977203+00:00
-- url     : https://prove2.me/submissions/a38d16f1-374f-4201-9f7d-7ced55aebd8a

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
theorem _root_.solution : pi0 + pi1 + pi2 = 1 := by norm_num [pi0, pi1, pi2]
end WeightedCacheParameters

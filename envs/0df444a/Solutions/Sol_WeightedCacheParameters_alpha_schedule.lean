-- Prove2me | solution 1 for WeightedCacheParameters.alpha_schedule
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:38:11.392414+00:00
-- url     : https://prove2.me/submissions/655ed3d0-2a64-43db-93b0-da47adb9db7b

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
theorem _root_.solution : alpha0 = pi0 + pi1 / 2 + pi2 / 3 ∧
    alpha1 = pi1 / 2 + pi2 / 3 ∧ alpha2 = pi2 / 3 := by
  norm_num [alpha0, alpha1, alpha2, pi0, pi1, pi2]
end WeightedCacheParameters

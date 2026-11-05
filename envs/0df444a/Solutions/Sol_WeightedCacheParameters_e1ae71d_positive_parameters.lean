-- Prove2me | solution 1 for WeightedCacheParameters_e1ae71d.positive_parameters
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:06:56.224756+00:00
-- url     : https://prove2.me/submissions/2f071705-9780-476a-87fb-078175b61e86

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
theorem _root_.solution :
    0 < pi0 ∧ 0 < pi1 ∧ 0 < pi2 ∧
    0 < yRoot ∧ yRoot < 1 ∧ 0 < zRoot ∧ zRoot < 1 ∧
    0 < cutSlope ∧ 0 < dropSlope := by
  norm_num [pi0, pi1, pi2, yRoot, zRoot, cutSlope, dropSlope]
end WeightedCacheParameters_e1ae71d

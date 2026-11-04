-- Prove2me | solution 1 for ThreeSum.WeightedGlobalCoverScale.global_representation_eventually
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:54:01.602724+00:00
-- url     : https://prove2.me/submissions/327613b8-40f0-46e7-ab22-b23d517961a7

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryCoverCapParameters
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Submission_Weighted_Global_TernaryCoverScale
import Theorems.Thm_ThreeSum_WeightedGlobalCoverScale_global_representation_budget

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalCoverScale
open TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters
open TernaryTypeLowerBound WeightedGlobalCoverCapParameters WeightedGlobalCoverFrequency
namespace ThreeSum.WeightedGlobalCoverScale
theorem _root_.solution (c d a : ℕ) (r : ℕ → ℕ)
    (hradix : ∀ᶠ n : ℕ in Filter.atTop, prime (scale 40000000000 c d)^(r n) ≤ a*n^3) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ((localFactor 40000000000 c d)^(r n) : ℝ) ≤ (n : ℝ)^(1/10000000000 : ℝ) := by
  filter_upwards [hradix, Filter.eventually_ge_atTop a] with n hr hn
  exact global_representation_budget c d a n (r n) hr hn
end ThreeSum.WeightedGlobalCoverScale

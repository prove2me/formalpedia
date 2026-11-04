-- Prove2me | solution 1 for ThreeSum.WeightedGlobalCoverScale.carry_factor_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:09:48.982224+00:00
-- url     : https://prove2.me/submissions/a1f618b8-fb8b-4203-99a9-ab9fb8245e7b

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryCoverCapParameters
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Submission_Weighted_Global_TernaryCoverScale

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalCoverScale
open TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters
open TernaryTypeLowerBound WeightedGlobalCoverCapParameters WeightedGlobalCoverFrequency
namespace ThreeSum.WeightedGlobalCoverScale
theorem _root_.solution (C c d b : ℕ)
    (hb : b ≤ c*(fixedLength (scale C c d)+1)^d) :
    b*(family (scale C c d) (momentOrder C)).length*
      rawThreshold (prime (scale C c d)) (sourceCap (scale C c d) (prime (scale C c d)))
        (momentOrder C) ≤ localFactor C c d := by
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hb)
end ThreeSum.WeightedGlobalCoverScale

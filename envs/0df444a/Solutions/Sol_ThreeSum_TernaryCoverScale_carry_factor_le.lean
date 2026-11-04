-- Prove2me | solution 1 for ThreeSum.TernaryCoverScale.carry_factor_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:56:52.849637+00:00
-- url     : https://prove2.me/submissions/648e1726-e42b-4342-be10-3b33dda0f797

import Definitions.Def_Submission_ThreeSum_TernaryCoverCapParameters
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Submission_ThreeSum_TernaryCoverScale

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverScale
open TernaryJointType TernaryCoverLocal TernaryLocalParameters
open TernaryTypeLowerBound TernaryCoverCapParameters TernaryCoverFrequency
namespace ThreeSum.TernaryCoverScale
theorem _root_.solution (C c d b : ℕ)
    (hb : b ≤ c*(fixedLength (scale C c d)+1)^d) :
    b*(family (scale C c d) (momentOrder C)).length*
      rawThreshold (prime (scale C c d)) (sourceCap (scale C c d) (prime (scale C c d)))
        (momentOrder C) ≤ localFactor C c d := by
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hb)
end ThreeSum.TernaryCoverScale

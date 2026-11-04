-- Prove2me | solution 1 for ThreeSum.TernaryCoverScale.polynomial_carry_representation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:37:47.793688+00:00
-- url     : https://prove2.me/submissions/6b227a76-1bfe-4b0e-ab51-4ad42c0165a0

import Definitions.Def_Submission_ThreeSum_TernaryCoverCapParameters
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Submission_ThreeSum_TernaryCoverScale
import Theorems.Thm_ThreeSum_TernaryCoverScale_fixed_representation_eventually
import Theorems.Thm_ThreeSum_TernaryCoverScale_carry_factor_le

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverScale
open TernaryJointType TernaryCoverLocal TernaryLocalParameters
open TernaryTypeLowerBound TernaryCoverCapParameters TernaryCoverFrequency
namespace ThreeSum.TernaryCoverScale
theorem _root_.solution (c d b : ℕ)
    (hb : b ≤ c*(fixedLength (scale 40000000000 c d)+1)^d) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ((b*(family (scale 40000000000 c d) (momentOrder 40000000000)).length*
        rawThreshold (prime (scale 40000000000 c d))
          (sourceCap (scale 40000000000 c d) (prime (scale 40000000000 c d)))
          (momentOrder 40000000000))^
          (radixLength (scale 40000000000 c d) n) : ℝ) ≤
        (n : ℝ)^(1/10000000000 : ℝ) := by
  filter_upwards [fixed_representation_eventually c d] with n hn
  have h := Nat.pow_le_pow_left (carry_factor_le 40000000000 c d b hb)
    (radixLength (scale 40000000000 c d) n)
  exact (by exact_mod_cast h : _ ≤ ((localFactor 40000000000 c d)^
    (radixLength (scale 40000000000 c d) n) : ℝ)).trans hn
end ThreeSum.TernaryCoverScale

-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCoverScale.polynomial_carry_representation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:40:45.895017+00:00
-- url     : https://prove2.me/submissions/8c1861c4-9270-411b-9549-06c56c052c58

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCoverCapParameters
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCoverScale
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalCoverScale_fixed_representation_eventually
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalCoverScale_carry_factor_le

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCoverScale
open TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters
open TernaryTypeLowerBound WeightedGlobalCoverCapParameters WeightedGlobalCoverFrequency
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCoverScale
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
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCoverScale

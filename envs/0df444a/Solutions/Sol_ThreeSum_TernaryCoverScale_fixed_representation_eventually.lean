-- Prove2me | solution 1 for ThreeSum.TernaryCoverScale.fixed_representation_eventually
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:47:11.338541+00:00
-- url     : https://prove2.me/submissions/f58bd626-77dd-4b87-9edd-3000458f50cc

import Definitions.Def_Submission_ThreeSum_TernaryCoverCapParameters
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Submission_ThreeSum_TernaryCoverScale
import Theorems.Thm_ThreeSum_TernaryCoverScale_scale_pos
import Theorems.Thm_ThreeSum_TernaryCoverScale_global_representation_eventually
import Theorems.Thm_ThreeSum_TernaryCoverScale_radix_power_upper

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverScale
open TernaryJointType TernaryCoverLocal TernaryLocalParameters
open TernaryTypeLowerBound TernaryCoverCapParameters TernaryCoverFrequency
namespace ThreeSum.TernaryCoverScale
theorem _root_.solution (c d : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ((localFactor 40000000000 c d)^
        (radixLength (scale 40000000000 c d) n) : ℝ) ≤
          (n : ℝ)^(1/10000000000 : ℝ) := by
  apply global_representation_eventually c d (outputSize (scale 40000000000 c d)^2)
  filter_upwards [Filter.eventually_gt_atTop (1 : ℕ)] with n hn
  exact radix_power_upper (scale_pos _ _ _) hn
end ThreeSum.TernaryCoverScale

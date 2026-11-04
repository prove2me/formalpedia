-- Prove2me | solution 1 for ThreeSum.WeightedGlobalCoverScale.threshold_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:04:36.832584+00:00
-- url     : https://prove2.me/submissions/fe067661-d2ef-459b-9a08-5e4009dc671c

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryCoverCapParameters
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Submission_Weighted_Global_TernaryCoverScale
import Theorems.Thm_ThreeSum_TernaryTypeLowerBound_vertices_lower_bound
import Theorems.Thm_ThreeSum_WeightedGlobalLocalParameters_fixedPi_space
import Theorems.Thm_ThreeSum_WeightedGlobalLocalParameters_fixedPi_total


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalCoverScale
open TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters
open TernaryTypeLowerBound WeightedGlobalCoverCapParameters WeightedGlobalCoverFrequency
namespace ThreeSum.WeightedGlobalCoverScale
theorem _root_.solution (m : ℕ) : 0 < threshold m := by
  have hR : 0 < 2^(fixedPi m 1)*3^(fixedPi m 2) := by positivity
  have hM := hR.trans_le (vertices_lower_bound (fixedPi m) (fixedPi_total m) (fixedPi_space m))
  exact Nat.mul_pos hM hR
end ThreeSum.WeightedGlobalCoverScale

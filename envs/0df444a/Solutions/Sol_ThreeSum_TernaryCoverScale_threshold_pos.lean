-- Prove2me | solution 1 for ThreeSum.TernaryCoverScale.threshold_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:04:51.909801+00:00
-- url     : https://prove2.me/submissions/901c09b0-7b25-429b-8681-daafee25774e

import Definitions.Def_Submission_ThreeSum_TernaryCoverCapParameters
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Submission_ThreeSum_TernaryCoverScale
import Theorems.Thm_ThreeSum_TernaryLocalParameters_fixedPi_space
import Theorems.Thm_ThreeSum_TernaryLocalParameters_fixedPi_total
import Theorems.Thm_ThreeSum_TernaryTypeLowerBound_vertices_lower_bound


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverScale
open TernaryJointType TernaryCoverLocal TernaryLocalParameters
open TernaryTypeLowerBound TernaryCoverCapParameters TernaryCoverFrequency
namespace ThreeSum.TernaryCoverScale
theorem _root_.solution (m : ℕ) : 0 < threshold m := by
  have hR : 0 < 2^(fixedPi m 1)*3^(fixedPi m 2) := by positivity
  have hM := hR.trans_le (vertices_lower_bound (fixedPi m) (fixedPi_total m) (fixedPi_space m))
  exact Nat.mul_pos hM hR
end ThreeSum.TernaryCoverScale

-- Prove2me | solution 1 for ThreeSum.WeightedGlobalCoverScale.partition_le_prime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:07:46.466206+00:00
-- url     : https://prove2.me/submissions/e1c0b78d-f988-4100-85f4-e0888a078976

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryCoverCapParameters
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Submission_Weighted_Global_TernaryCoverScale
import Theorems.Thm_ThreeSum_WeightedGlobalCoverScale_prime_lower
import Theorems.Thm_ThreeSum_TernaryTypeLowerBound_partition_cap_le_prime
import Theorems.Thm_ThreeSum_WeightedGlobalLocalParameters_fixedPi_space
import Theorems.Thm_ThreeSum_WeightedGlobalLocalParameters_fixedPi_total


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalCoverScale
open TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters
open TernaryTypeLowerBound WeightedGlobalCoverCapParameters WeightedGlobalCoverFrequency
namespace ThreeSum.WeightedGlobalCoverScale
theorem _root_.solution (m : ℕ) : 2^(fixedPi m 1)*3^(fixedPi m 2) ≤ prime m :=
  partition_cap_le_prime (fixedPi m) (fixedPi_total m) (fixedPi_space m) (prime m) (prime_lower m)
end ThreeSum.WeightedGlobalCoverScale

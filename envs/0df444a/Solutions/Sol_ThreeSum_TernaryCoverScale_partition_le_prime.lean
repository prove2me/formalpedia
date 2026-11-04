-- Prove2me | solution 1 for ThreeSum.TernaryCoverScale.partition_le_prime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:07:45.282579+00:00
-- url     : https://prove2.me/submissions/37d670ee-5d40-4853-b333-a26a61e9cd6e

import Definitions.Def_Submission_ThreeSum_TernaryCoverCapParameters
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Submission_ThreeSum_TernaryCoverScale
import Theorems.Thm_ThreeSum_TernaryCoverScale_prime_lower
import Theorems.Thm_ThreeSum_TernaryLocalParameters_fixedPi_space
import Theorems.Thm_ThreeSum_TernaryLocalParameters_fixedPi_total
import Theorems.Thm_ThreeSum_TernaryTypeLowerBound_partition_cap_le_prime


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverScale
open TernaryJointType TernaryCoverLocal TernaryLocalParameters
open TernaryTypeLowerBound TernaryCoverCapParameters TernaryCoverFrequency
namespace ThreeSum.TernaryCoverScale
theorem _root_.solution (m : ℕ) : 2^(fixedPi m 1)*3^(fixedPi m 2) ≤ prime m :=
  partition_cap_le_prime (fixedPi m) (fixedPi_total m) (fixedPi_space m) (prime m) (prime_lower m)
end ThreeSum.TernaryCoverScale

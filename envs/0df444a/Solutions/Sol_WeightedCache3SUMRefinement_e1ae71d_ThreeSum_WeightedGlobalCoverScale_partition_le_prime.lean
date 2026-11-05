-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCoverScale.partition_le_prime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:26:42.814958+00:00
-- url     : https://prove2.me/submissions/71734761-b562-4cc5-a197-b3afac07af01

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCoverCapParameters
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCoverScale
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalCoverScale_prime_lower
import Theorems.Thm_ThreeSum_TernaryTypeLowerBound_partition_cap_le_prime
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalLocalParameters_fixedPi_space
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalLocalParameters_fixedPi_total


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCoverScale
open TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters
open TernaryTypeLowerBound WeightedGlobalCoverCapParameters WeightedGlobalCoverFrequency
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCoverScale
theorem _root_.solution (m : ℕ) : 2^(fixedPi m 1)*3^(fixedPi m 2) ≤ prime m :=
  partition_cap_le_prime (fixedPi m) (fixedPi_total m) (fixedPi_space m) (prime m) (prime_lower m)
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCoverScale

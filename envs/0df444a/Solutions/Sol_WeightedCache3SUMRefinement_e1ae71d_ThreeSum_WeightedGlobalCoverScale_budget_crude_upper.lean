-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCoverScale.budget_crude_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:30:14.871862+00:00
-- url     : https://prove2.me/submissions/0b21c2e5-4a95-42ed-aad2-4a3776af610d

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCoverCapParameters
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCoverScale
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalCoverScale_prime_crude_upper
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalCoverScale_sourceCap_crude_upper
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalCoverScale_log2_le_of_le_pow

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCoverScale
open TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters
open TernaryTypeLowerBound WeightedGlobalCoverCapParameters WeightedGlobalCoverFrequency
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCoverScale
theorem _root_.solution (m k : ℕ) :
    capBudget (prime m) (sourceCap m (prime m)) k ≤ 12*fixedLength m+8*k^2+26 := by
  have hp := log2_le_of_le_pow (prime_crude_upper m)
  have hB := log2_le_of_le_pow (sourceCap_crude_upper m)
  unfold capBudget
  omega
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCoverScale

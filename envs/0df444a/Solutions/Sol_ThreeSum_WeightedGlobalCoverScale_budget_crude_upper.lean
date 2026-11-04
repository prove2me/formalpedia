-- Prove2me | solution 1 for ThreeSum.WeightedGlobalCoverScale.budget_crude_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:23:37.761193+00:00
-- url     : https://prove2.me/submissions/134b03e5-3975-46a5-914f-ce38121c1e3e

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryCoverCapParameters
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Submission_Weighted_Global_TernaryCoverScale
import Theorems.Thm_ThreeSum_WeightedGlobalCoverScale_prime_crude_upper
import Theorems.Thm_ThreeSum_WeightedGlobalCoverScale_sourceCap_crude_upper
import Theorems.Thm_ThreeSum_WeightedGlobalCoverScale_log2_le_of_le_pow

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalCoverScale
open TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters
open TernaryTypeLowerBound WeightedGlobalCoverCapParameters WeightedGlobalCoverFrequency
namespace ThreeSum.WeightedGlobalCoverScale
theorem _root_.solution (m k : ℕ) :
    capBudget (prime m) (sourceCap m (prime m)) k ≤ 12*fixedLength m+8*k^2+26 := by
  have hp := log2_le_of_le_pow (prime_crude_upper m)
  have hB := log2_le_of_le_pow (sourceCap_crude_upper m)
  unfold capBudget
  omega
end ThreeSum.WeightedGlobalCoverScale

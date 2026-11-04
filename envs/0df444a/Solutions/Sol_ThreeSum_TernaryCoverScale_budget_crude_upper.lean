-- Prove2me | solution 1 for ThreeSum.TernaryCoverScale.budget_crude_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:19:42.496747+00:00
-- url     : https://prove2.me/submissions/21b5ca50-141a-4731-a96d-4c1bc7c90c42

import Definitions.Def_Submission_ThreeSum_TernaryCoverCapParameters
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Submission_ThreeSum_TernaryCoverScale
import Theorems.Thm_ThreeSum_TernaryCoverScale_prime_crude_upper
import Theorems.Thm_ThreeSum_TernaryCoverScale_sourceCap_crude_upper
import Theorems.Thm_ThreeSum_TernaryCoverScale_log2_le_of_le_pow

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverScale
open TernaryJointType TernaryCoverLocal TernaryLocalParameters
open TernaryTypeLowerBound TernaryCoverCapParameters TernaryCoverFrequency
namespace ThreeSum.TernaryCoverScale
theorem _root_.solution (m k : ℕ) :
    capBudget (prime m) (sourceCap m (prime m)) k ≤ 12*fixedLength m+8*k^2+26 := by
  have hp := log2_le_of_le_pow (prime_crude_upper m)
  have hB := log2_le_of_le_pow (sourceCap_crude_upper m)
  unfold capBudget
  omega
end ThreeSum.TernaryCoverScale

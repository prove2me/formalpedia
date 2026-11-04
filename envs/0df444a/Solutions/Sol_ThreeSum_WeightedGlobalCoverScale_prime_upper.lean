-- Prove2me | solution 1 for ThreeSum.WeightedGlobalCoverScale.prime_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:14:52.052199+00:00
-- url     : https://prove2.me/submissions/ea8618f9-76fa-4c83-8ec5-d8650fdb7a26

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryCoverCapParameters
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Submission_Weighted_Global_TernaryCoverScale
import Theorems.Thm_ThreeSum_WeightedGlobalCoverScale_threshold_pos
import Theorems.Thm_ThreeSum_LocalCoverBounds_selectedPrime_sq_upper


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalCoverScale
open TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters
open TernaryTypeLowerBound WeightedGlobalCoverCapParameters WeightedGlobalCoverFrequency
namespace ThreeSum.WeightedGlobalCoverScale
theorem _root_.solution (m : ℕ) : prime m^2 ≤ 16*threshold m :=
  LocalCoverBounds.selectedPrime_sq_upper (threshold_pos m)
end ThreeSum.WeightedGlobalCoverScale

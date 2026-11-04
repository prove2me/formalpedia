-- Prove2me | solution 1 for ThreeSum.WeightedGlobalCoverScale.prime_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:54:56.06852+00:00
-- url     : https://prove2.me/submissions/cd165ff6-3777-4786-abfc-90cf9767d77f

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryCoverCapParameters
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Submission_Weighted_Global_TernaryCoverScale
import Theorems.Thm_ThreeSum_LocalCoverBounds_selectedPrime_sq_lower


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalCoverScale
open TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters
open TernaryTypeLowerBound WeightedGlobalCoverCapParameters WeightedGlobalCoverFrequency
namespace ThreeSum.WeightedGlobalCoverScale
theorem _root_.solution (m : ℕ) : threshold m ≤ prime m^2 :=
  LocalCoverBounds.selectedPrime_sq_lower _
end ThreeSum.WeightedGlobalCoverScale

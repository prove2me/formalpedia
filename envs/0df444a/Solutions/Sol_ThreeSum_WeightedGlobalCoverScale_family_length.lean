-- Prove2me | solution 1 for ThreeSum.WeightedGlobalCoverScale.family_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:14:53.598625+00:00
-- url     : https://prove2.me/submissions/6a007a92-a714-423c-be81-952b7201f6ab

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryCoverCapParameters
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Submission_Weighted_Global_TernaryCoverScale
import Theorems.Thm_ThreeSum_Cover_greedyChoices_length


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalCoverScale
open TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters
open TernaryTypeLowerBound WeightedGlobalCoverCapParameters WeightedGlobalCoverFrequency
namespace ThreeSum.WeightedGlobalCoverScale
theorem _root_.solution (m k : ℕ) :
    (family m k).length = frequencyFactor m*(Nat.log2 (prime m^2)+1) :=
  Cover.greedyChoices_length _ _ _ _
end ThreeSum.WeightedGlobalCoverScale

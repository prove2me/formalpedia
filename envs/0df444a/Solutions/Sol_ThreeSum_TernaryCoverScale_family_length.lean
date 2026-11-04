-- Prove2me | solution 1 for ThreeSum.TernaryCoverScale.family_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:56:49.088131+00:00
-- url     : https://prove2.me/submissions/dd77e247-1c25-42c0-9d5a-22cc103a382e

import Definitions.Def_Submission_ThreeSum_TernaryCoverCapParameters
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Submission_ThreeSum_TernaryCoverScale
import Theorems.Thm_ThreeSum_Cover_greedyChoices_length


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverScale
open TernaryJointType TernaryCoverLocal TernaryLocalParameters
open TernaryTypeLowerBound TernaryCoverCapParameters TernaryCoverFrequency
namespace ThreeSum.TernaryCoverScale
theorem _root_.solution (m k : ℕ) :
    (family m k).length = frequencyFactor m*(Nat.log2 (prime m^2)+1) :=
  Cover.greedyChoices_length _ _ _ _
end ThreeSum.TernaryCoverScale

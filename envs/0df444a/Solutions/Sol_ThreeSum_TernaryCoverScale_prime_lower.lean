-- Prove2me | solution 1 for ThreeSum.TernaryCoverScale.prime_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:54:55.010194+00:00
-- url     : https://prove2.me/submissions/6463d6c0-cec6-48c7-b43a-dbb7e7fb2503

import Definitions.Def_Submission_ThreeSum_TernaryCoverCapParameters
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Submission_ThreeSum_TernaryCoverScale
import Theorems.Thm_ThreeSum_LocalCoverBounds_selectedPrime_sq_lower


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverScale
open TernaryJointType TernaryCoverLocal TernaryLocalParameters
open TernaryTypeLowerBound TernaryCoverCapParameters TernaryCoverFrequency
namespace ThreeSum.TernaryCoverScale
theorem _root_.solution (m : ℕ) : threshold m ≤ prime m^2 :=
  LocalCoverBounds.selectedPrime_sq_lower _
end ThreeSum.TernaryCoverScale

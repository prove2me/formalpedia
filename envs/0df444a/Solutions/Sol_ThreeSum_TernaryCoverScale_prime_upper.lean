-- Prove2me | solution 1 for ThreeSum.TernaryCoverScale.prime_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:08:46.569672+00:00
-- url     : https://prove2.me/submissions/e4cebf9d-d1da-41d9-b692-fd25262bef78

import Definitions.Def_Submission_ThreeSum_TernaryCoverCapParameters
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Submission_ThreeSum_TernaryCoverScale
import Theorems.Thm_ThreeSum_TernaryCoverScale_threshold_pos
import Theorems.Thm_ThreeSum_LocalCoverBounds_selectedPrime_sq_upper


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverScale
open TernaryJointType TernaryCoverLocal TernaryLocalParameters
open TernaryTypeLowerBound TernaryCoverCapParameters TernaryCoverFrequency
namespace ThreeSum.TernaryCoverScale
theorem _root_.solution (m : ℕ) : prime m^2 ≤ 16*threshold m :=
  LocalCoverBounds.selectedPrime_sq_upper (threshold_pos m)
end ThreeSum.TernaryCoverScale

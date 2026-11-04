-- Prove2me | solution 1 for ThreeSum.WeightedGlobalCoverScale.log2_le_of_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:38:50.047229+00:00
-- url     : https://prove2.me/submissions/8ca7f96b-e058-4810-b746-ff4496997826

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryCoverCapParameters
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Submission_Weighted_Global_TernaryCoverScale

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalCoverScale
open TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters
open TernaryTypeLowerBound WeightedGlobalCoverCapParameters WeightedGlobalCoverFrequency
namespace ThreeSum.WeightedGlobalCoverScale
theorem _root_.solution {x e : ℕ} (h : x ≤ 2^e) : Nat.log2 x ≤ e := by
  rw [Nat.log2_eq_log_two]
  exact (Nat.log_mono_right h).trans_eq (Nat.log_pow (by decide) _)
end ThreeSum.WeightedGlobalCoverScale

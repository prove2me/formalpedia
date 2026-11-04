-- Prove2me | solution 1 for ThreeSum.TernaryCoverScale.log2_le_of_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:02:44.384498+00:00
-- url     : https://prove2.me/submissions/a9edb112-570d-47b6-8fbf-1bd37a819e04

import Definitions.Def_Submission_ThreeSum_TernaryCoverCapParameters
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Submission_ThreeSum_TernaryCoverScale

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverScale
open TernaryJointType TernaryCoverLocal TernaryLocalParameters
open TernaryTypeLowerBound TernaryCoverCapParameters TernaryCoverFrequency
namespace ThreeSum.TernaryCoverScale
theorem _root_.solution {x e : ℕ} (h : x ≤ 2^e) : Nat.log2 x ≤ e := by
  rw [Nat.log2_eq_log_two]
  exact (Nat.log_mono_right h).trans_eq (Nat.log_pow (by decide) _)
end ThreeSum.TernaryCoverScale

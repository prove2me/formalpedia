-- Prove2me | solution 1 for ThreeSum.TernaryCoverScale.capExponent_mul_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:24:27.263257+00:00
-- url     : https://prove2.me/submissions/0250afa4-1f57-4a97-8b58-e36c9fd4d071

import Definitions.Def_Submission_ThreeSum_TernaryCoverCapParameters
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Submission_ThreeSum_TernaryCoverScale
import Theorems.Thm_ThreeSum_TernaryCoverScale_budget_crude_upper

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverScale
open TernaryJointType TernaryCoverLocal TernaryLocalParameters
open TernaryTypeLowerBound TernaryCoverCapParameters TernaryCoverFrequency
namespace ThreeSum.TernaryCoverScale
theorem _root_.solution (m k : ℕ) :
    k*capExponent (prime m) (sourceCap m (prime m)) k ≤ 12*fixedLength m+8*k^2+26+k := by
  have hd := Nat.div_mul_le_self (capBudget (prime m) (sourceCap m (prime m)) k+k-1) k
  have hb := budget_crude_upper m k
  unfold capExponent
  rw [Nat.ceilDiv_eq_add_pred_div]
  rw [Nat.mul_comm] at hd
  omega
end ThreeSum.TernaryCoverScale

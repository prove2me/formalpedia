-- Prove2me | solution 1 for ThreeSum.LocalCoverBounds.groupSize_lt_localPrime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:11:06.724225+00:00
-- url     : https://prove2.me/submissions/7814af1a-ff32-4911-b8f8-b042c6032498

import Definitions.Def_Submission_ThreeSum_LayerCounts
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Sqrt
import Mathlib.NumberTheory.Bertrand
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Theorems.Thm_ThreeSum_LocalCoverBounds_concrete_output_gt_pow
import Theorems.Thm_ThreeSum_LocalCoverBounds_groupSize_lt_modulus
import Theorems.Thm_ThreeSum_LocalCoverBounds_localPrime_sq_lower

set_option autoImplicit false
open ThreeSum ThreeSum.LocalCoverBounds
open scoped BigOperators
namespace ThreeSum.LocalCoverBounds
theorem _root_.solution {h : ℕ} (hh : 0 < h) : groupSize h < localPrime h :=
  groupSize_lt_modulus (concrete_output_gt_pow hh) (localPrime_sq_lower h)
end ThreeSum.LocalCoverBounds

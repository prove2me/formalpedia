-- Prove2me | solution 1 for ThreeSum.LocalCoverBounds.le_rootCeiling_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:13:17.926984+00:00
-- url     : https://prove2.me/submissions/f07d8be3-509b-4e12-a042-cf0ec5cabcc3

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
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices



set_option autoImplicit false
open ThreeSum ThreeSum.LocalCoverBounds
open scoped BigOperators
namespace ThreeSum.LocalCoverBounds
theorem _root_.solution (N : ℕ) : N ≤ rootCeiling N ^ 2 := by
  have hs := Nat.lt_succ_sqrt' (N - 1)
  simp only [Nat.succ_eq_add_one] at hs
  unfold rootCeiling
  omega
end ThreeSum.LocalCoverBounds

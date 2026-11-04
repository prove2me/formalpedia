-- Prove2me | solution 1 for ThreeSum.LocalCoverBounds.groupSize_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:13:15.319273+00:00
-- url     : https://prove2.me/submissions/21473fe0-5dbb-455a-9c54-3e7f91fe2786

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
theorem _root_.solution (h : ℕ) :
    2 ^ (2 * h) ≤ (2 * h + 1) * groupSize h := by
  simpa only [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul,
    groupSize] using Nat.four_pow_le_two_mul_add_one_mul_central_binom h
end ThreeSum.LocalCoverBounds

-- Prove2me | solution 1 for SmallRatio.sum_sq_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:15:27.687802+00:00
-- url     : https://prove2.me/submissions/7677993c-cb57-4aaa-be60-96f6d58f2be6

module
public import Definitions.Def_SmallRatio_Defs
public import Definitions.Def_SmallRatio_Reciprocity

set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
namespace SmallRatio
theorem _root_.solution (m : ℕ) : 6 * ∑ r ∈ range m, (r : ℚ) ^ 2 = ((m : ℚ) - 1) * m * (2 * m - 1) := by
  induction m with
  | zero => simp
  | succ m ih => rw [sum_range_succ, mul_add, ih]; push_cast; ring
end SmallRatio

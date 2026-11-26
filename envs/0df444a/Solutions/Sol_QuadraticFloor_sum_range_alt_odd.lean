-- Prove2me | solution 1 for QuadraticFloor.sum_range_alt_odd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:53:57.534124+00:00
-- url     : https://prove2.me/submissions/782ccfdc-cfb2-4388-b90a-f049ca027992

module
public import Definitions.Def_QuadraticFloor_Defs
public import Definitions.Def_QuadraticFloor_RootCount

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
namespace QuadraticFloor
theorem _root_.solution (m : ℕ) : ∑ r ∈ range (2 * m + 1), (-1 : ℤ) ^ r = 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      (odd_two_mul_add_one m).neg_one_pow, (show Even (2 * m + 1 + 1) from ⟨m + 1, by ring⟩).neg_one_pow]
    ring
end QuadraticFloor

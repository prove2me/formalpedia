-- Prove2me | solution 1 for QuarterSumLadder.sq_add_sq_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:55:06.179518+00:00
-- url     : https://prove2.me/submissions/70723f73-4c9d-41f9-808d-62026c3399d5

module
public import Mathlib
public import Definitions.Def_QuarterSumLadder_Arith

set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
namespace QuarterSumLadder
theorem _root_.solution {x y : ℤ} (hx : x % 2 = 0) (hy : y % 2 = 0) :
    x ^ 2 + y ^ 2 = 4 * ((x / 2) ^ 2 + (y / 2) ^ 2) := by
  obtain ⟨a, rfl⟩ : ∃ a, x = 2 * a := ⟨x / 2, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, y = 2 * b := ⟨y / 2, by omega⟩
  rw [Int.mul_ediv_cancel_left _ two_ne_zero, Int.mul_ediv_cancel_left _ two_ne_zero]; ring
end QuarterSumLadder

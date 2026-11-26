-- Prove2me | solution 1 for QuarterSumLadder.even_even_eight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:03:05.455066+00:00
-- url     : https://prove2.me/submissions/9275e27c-7fcc-48fe-ba10-edcfa422b9a7

module
public import Mathlib
public import Definitions.Def_QuarterSumLadder_Arith
public import Theorems.Thm_QuarterSumLadder_sq_mod_two
public import Theorems.Thm_QuarterSumLadder_sq_add_sq_even

set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
namespace QuarterSumLadder
theorem _root_.solution {x y : ℤ} (hx : x % 2 = 0) (hy : y % 2 = 0) :
    (4 : ℤ) ∣ x ^ 2 + y ^ 2 ∧ ((8 : ℤ) ∣ x ^ 2 + y ^ 2 ↔ (4 : ℤ) ∣ x - y) := by
  rw [sq_add_sq_even hx hy]
  refine ⟨dvd_mul_right 4 _, ?_⟩
  have h1 := sq_mod_two (x / 2); have h2 := sq_mod_two (y / 2)
  omega
end QuarterSumLadder

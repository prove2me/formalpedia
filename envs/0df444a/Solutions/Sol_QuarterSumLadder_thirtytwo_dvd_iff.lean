-- Prove2me | solution 1 for QuarterSumLadder.thirtytwo_dvd_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:04:04.90765+00:00
-- url     : https://prove2.me/submissions/461f4665-42a6-4566-a1a2-e1f5086e8a53

module
public import Mathlib
public import Definitions.Def_QuarterSumLadder_Arith
public import Theorems.Thm_QuarterSumLadder_sq_mod_two

set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
namespace QuarterSumLadder
theorem _root_.solution {x y : ℤ} (hx : (4 : ℤ) ∣ x) (hy : (4 : ℤ) ∣ y) :
    (32 : ℤ) ∣ x ^ 2 + y ^ 2 ↔ (8 : ℤ) ∣ x + y := by
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := hy
  have h : (4 * u) ^ 2 + (4 * v) ^ 2 = 16 * (u ^ 2 + v ^ 2) := by ring
  rw [h]
  have h1 := sq_mod_two u; have h2 := sq_mod_two v
  omega
end QuarterSumLadder

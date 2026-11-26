-- Prove2me | solution 1 for QuarterSumLadder.sixteen_dvd_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:03:08.337238+00:00
-- url     : https://prove2.me/submissions/47f7c3c6-ab82-455d-b092-c170f872b851

module
public import Mathlib
public import Definitions.Def_QuarterSumLadder_Arith
public import Theorems.Thm_QuarterSumLadder_sq_mod_two
public import Theorems.Thm_QuarterSumLadder_sq_add_sq_odd
public import Theorems.Thm_QuarterSumLadder_sq_add_sq_mixed
public import Theorems.Thm_QuarterSumLadder_sq_add_sq_even

set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
namespace QuarterSumLadder
theorem _root_.solution (x y : ℤ) : (16 : ℤ) ∣ x ^ 2 + y ^ 2 ↔ (4 : ℤ) ∣ x ∧ (4 : ℤ) ∣ y := by
  rcases Int.emod_two_eq_zero_or_one x with hx | hx <;>
    rcases Int.emod_two_eq_zero_or_one y with hy | hy
  · rw [sq_add_sq_even hx hy]
    have h1 := sq_mod_two (x / 2); have h2 := sq_mod_two (y / 2)
    rcases Int.emod_two_eq_zero_or_one (x / 2) with ha | ha <;>
      rcases Int.emod_two_eq_zero_or_one (y / 2) with hb | hb
    · obtain ⟨a, ha'⟩ : ∃ a, x / 2 = 2 * a := ⟨x / 2 / 2, by omega⟩
      obtain ⟨b, hb'⟩ : ∃ b, y / 2 = 2 * b := ⟨y / 2 / 2, by omega⟩
      rw [ha', hb']
      constructor
      · intro _; omega
      · intro _; exact ⟨a ^ 2 + b ^ 2, by ring⟩
    · have := sq_add_sq_mixed (x := y / 2) (y := x / 2) hb ha; omega
    · have := sq_add_sq_mixed ha hb; omega
    · have := sq_add_sq_odd ha hb; omega
  · have := sq_add_sq_mixed (x := y) (y := x) hy hx; omega
  · have := sq_add_sq_mixed hx hy; omega
  · have := sq_add_sq_odd hx hy; omega
end QuarterSumLadder

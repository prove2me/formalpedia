-- Prove2me | solution 1 for QuarterSumLadder.char_eq_one_iff_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:06:14.482897+00:00
-- url     : https://prove2.me/submissions/0325a58f-9edb-4f8f-a90c-29e28c6c59c3

module
public import Definitions.Def_QuarterSumLadder_Classes
public import Definitions.Def_QuarterSumLadder_Counts
public import Theorems.Thm_QuarterSumLadder_exists_generator
public import Theorems.Thm_QuarterSumLadder_gi_im
public import Theorems.Thm_QuarterSumLadder_gi_pow_eq_one_iff
public import Theorems.Thm_QuarterSumLadder_gi_re
public import Theorems.Thm_QuarterSumLadder_mod_eight_aux
public import Theorems.Thm_QuarterSumLadder_quartic_apply_generator
public import Theorems.Thm_QuarterSumLadder_seventeen_le
attribute [local simp] QuarterSumLadder.gi_im
attribute [local simp] QuarterSumLadder.gi_re



set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4)
include hp8 hχ
namespace QuarterSumLadder
theorem _root_.solution {x : ZMod p} (hx : x ≠ 0) : χ x = 1 ↔ x ^ Q p = 1 := by
  have hpq := mod_eight_aux hp8
  have hQ : 0 < Q p := by have := seventeen_le hp8; omega
  obtain ⟨g, hgo, hg⟩ := exists_generator (p := p)
  obtain ⟨j, hj⟩ := hg (Units.mk0 x hx)
  have hxj : x = (g : ZMod p) ^ j := by
    have := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) hj
    simp only [Units.val_pow_eq_pow_val, Units.val_mk0] at this
    exact this.symm
  rw [hxj, map_pow, gi_pow_eq_one_iff (quartic_apply_generator χ hχ hg), ← pow_mul,
    ← Units.val_pow_eq_pow_val, Units.val_eq_one, ← orderOf_dvd_iff_pow_eq_one, hgo, hpq,
    show j * Q p = Q p * j by ring, mul_comm 4 (Q p)]
  exact (Nat.mul_dvd_mul_iff_left hQ).symm
end QuarterSumLadder

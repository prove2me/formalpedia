-- Prove2me | solution 1 for P2M_FixedOrderFactor_sum_char_all__ce659e42cafe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:00:25.207791+00:00
-- url     : https://prove2.me/submissions/586ee947-3c93-49fb-a989-29753fe18659

module
public import Mathlib
public import Definitions.Def_FixedOrderFactor_Characters

set_option autoImplicit true
@[expose] public section
public section
open Finset
open FixedOrderFactor
variable (p : ℕ) [Fact p.Prime]
namespace FixedOrderFactor
theorem _root_.solution {m n : ℕ} (hmn : m ≠ n) (hm : m < p) (hn : n < p) (hn0 : n ≠ 0) :
    ∑ χ : DirichletCharacter ℂ p, χ m * starRingEnd ℂ (χ n) = 0 := by
  have hnu : (n : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun h => hn0 (Nat.eq_zero_of_dvd_of_lt h hn)
  have hterm : ∀ χ : DirichletCharacter ℂ p, χ m * starRingEnd ℂ (χ n) =
      χ ((n : ZMod p)⁻¹) * χ m := by
    intro χ
    rw [show starRingEnd ℂ (χ n) = star (χ n) from rfl, MulChar.star_apply',
      MulChar.inv_apply', mul_comm]
  simp_rw [hterm]
  rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ (isUnit_iff_ne_zero.mpr hnu), if_neg]
  intro h
  apply hmn
  have := (ZMod.natCast_eq_natCast_iff' n m p).mp h
  rw [Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hm] at this
  exact this.symm
end FixedOrderFactor

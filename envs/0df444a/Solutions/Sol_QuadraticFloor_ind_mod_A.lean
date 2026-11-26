-- Prove2me | solution 1 for QuadraticFloor.ind_mod_A
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:56:17.222488+00:00
-- url     : https://prove2.me/submissions/0f25e3d5-aad0-432f-b90d-45e6ff9a868b

module
public import Definitions.Def_QuadraticFloor_HalfPeriod
public import Definitions.Def_QuadraticFloor_SquareClass
public import Theorems.Thm_QuadraticFloor_isUnit_intCast_of_gcd
public import Theorems.Thm_QuadraticFloor_char_inv_eq_star

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
namespace QuadraticFloor
theorem _root_.solution {A : ℕ} [NeZero A] {B : ℤ} (hB : Int.gcd B A = 1) {d : ℕ}
    (hd : (d : ZMod A) = (B : ZMod A) ^ 2) (x : ℕ) :
    (if x % A = d % A then (1 : ℂ) else 0) =
      (1 / (A.totient : ℂ)) *
        ∑ ψ : DirichletCharacter ℂ A, (starRingEnd ℂ (ψ (B : ZMod A))) ^ 2 * ψ (x : ZMod A) := by
  have hu : IsUnit (d : ZMod A) := by rw [hd]; exact (isUnit_intCast_of_gcd hB).pow 2
  have horth := DirichletCharacter.sum_char_inv_mul_char_eq ℂ hu (x : ZMod A)
  have hw : ∀ ψ : DirichletCharacter ℂ A,
      ψ (d : ZMod A)⁻¹ = (starRingEnd ℂ (ψ (B : ZMod A))) ^ 2 := by
    intro ψ
    rw [char_inv_eq_star ψ hu, hd, map_pow, star_pow, starRingEnd_apply]
  simp_rw [hw] at horth
  rw [horth]
  have htot : (A.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne A))).ne'
  by_cases h : x % A = d % A
  · have : (d : ZMod A) = x := (ZMod.natCast_eq_natCast_iff' d x A).2 h.symm
    simp only [h, this, ite_true]
    field_simp
  · have : (d : ZMod A) ≠ x := fun e => h ((ZMod.natCast_eq_natCast_iff' d x A).1 e).symm
    simp only [h, this, ite_false, mul_zero]
end QuadraticFloor

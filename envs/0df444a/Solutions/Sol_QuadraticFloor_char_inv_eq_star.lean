-- Prove2me | solution 1 for QuadraticFloor.char_inv_eq_star
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:55:06.965851+00:00
-- url     : https://prove2.me/submissions/bd42d391-a2cd-438a-a9c8-4c1db259252c

module
public import Definitions.Def_QuadraticFloor_HalfPeriod
public import Definitions.Def_QuadraticFloor_SquareClass

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
namespace QuadraticFloor
theorem _root_.solution {A : ℕ} [NeZero A] (ψ : DirichletCharacter ℂ A) {a : ZMod A}
    (ha : IsUnit a) : ψ a⁻¹ = star (ψ a) := by
  have h1 : ψ a⁻¹ * ψ a = 1 := by rw [← map_mul, mul_comm, ZMod.mul_inv_of_unit a ha, map_one]
  have h2 : star (ψ a) * ψ a = 1 := by
    rw [← MulChar.star_apply, MulChar.star_eq_inv, ← MulChar.mul_apply, MulChar.inv_mul,
      MulChar.one_apply ha]
  have h3 : ψ a ≠ 0 := by intro h; rw [h, mul_zero] at h1; exact zero_ne_one h1
  exact mul_right_cancel₀ h3 (h1.trans h2.symm)
end QuadraticFloor

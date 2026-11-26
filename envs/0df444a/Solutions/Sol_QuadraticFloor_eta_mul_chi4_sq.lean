-- Prove2me | solution 1 for QuadraticFloor.eta_mul_chi4_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:46:05.448965+00:00
-- url     : https://prove2.me/submissions/49b5161d-28a2-4692-8b37-d632e017c0f5

module
public import Definitions.Def_QuadraticFloor_HalfPeriod
public import Definitions.Def_QuadraticFloor_SquareClass
public import Theorems.Thm_QuadraticFloor_eta_of_even


set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {A : ℕ}
namespace QuadraticFloor
theorem _root_.solution (p x : ℕ) : (eta p x : ℂ) * (ZMod.χ₄ (x : ZMod 4) : ℂ) ^ 2 = eta p x := by
  by_cases hx : Even x
  · simp [eta_of_even hx]
  · have hx2 : x % 2 = 1 := Nat.odd_iff.1 (Nat.not_even_iff_odd.1 hx)
    rw [ZMod.χ₄_nat_eq_if_mod_four]
    have : x % 4 = 1 ∨ x % 4 = 3 := by omega
    rcases this with h | h <;> simp [h, hx2]
end QuadraticFloor

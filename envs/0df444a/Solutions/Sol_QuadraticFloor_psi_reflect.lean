-- Prove2me | solution 1 for QuadraticFloor.psi_reflect
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:55:27.725334+00:00
-- url     : https://prove2.me/submissions/972cf48a-2836-47b3-91e9-4c4f8684caba

module
public import Definitions.Def_QuadraticFloor_HalfPeriod
public import Definitions.Def_QuadraticFloor_SquareClass
public import Theorems.Thm_QuadraticFloor_cast_sub_of_dvd

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
namespace QuadraticFloor
theorem _root_.solution {A : ℕ} (ψ : DirichletCharacter ℂ A) {q x : ℕ} (hx : x ≤ q) (hq : A ∣ q) :
    ψ ((q - x : ℕ) : ZMod A) = ψ (-1) * ψ (x : ZMod A) := by
  rw [cast_sub_of_dvd A hx hq, ← map_mul, neg_one_mul]
end QuadraticFloor

-- Prove2me | solution 1 for QuadraticFloor.chi4_reflect
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:56:30.867835+00:00
-- url     : https://prove2.me/submissions/9f35c09e-2f9a-4488-84a5-ab0e66719fd4

module
public import Definitions.Def_QuadraticFloor_HalfPeriod
public import Definitions.Def_QuadraticFloor_SquareClass
public import Theorems.Thm_QuadraticFloor_cast_sub_of_dvd

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {A : ℕ}
namespace QuadraticFloor
theorem _root_.solution (A p : ℕ) {x : ℕ} (hx : x ≤ 8 * A * p) :
    ZMod.χ₄ ((8 * A * p - x : ℕ) : ZMod 4) = -ZMod.χ₄ (x : ZMod 4) := by
  rw [cast_sub_of_dvd 4 hx ⟨2 * A * p, by ring⟩]
  generalize (x : ZMod 4) = y
  revert y; decide
end QuadraticFloor

-- Prove2me | solution 1 for QuadraticFloor.chi4_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:50:33.459796+00:00
-- url     : https://prove2.me/submissions/7508a35f-c459-4a11-8e41-c7e23694fc77

module
public import Definitions.Def_QuadraticFloor_HalfPeriod
public import Definitions.Def_QuadraticFloor_SquareClass
public import Theorems.Thm_QuadraticFloor_cast_add_of_dvd

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {A : ℕ}
namespace QuadraticFloor
theorem _root_.solution (A p x : ℕ) : ZMod.χ₄ ((x + 4 * A * p : ℕ) : ZMod 4) = ZMod.χ₄ (x : ZMod 4) := by
  rw [cast_add_of_dvd x _ 4 ⟨A * p, by ring⟩]
end QuadraticFloor

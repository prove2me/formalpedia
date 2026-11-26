-- Prove2me | solution 1 for QuadraticFloor.vartheta_add_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:57:13.487685+00:00
-- url     : https://prove2.me/submissions/f493e27a-bac3-4a4d-b354-0fe2dfdae4bf

module
public import Definitions.Def_QuadraticFloor_HalfPeriod
public import Definitions.Def_QuadraticFloor_SquareClass
public import Theorems.Thm_QuadraticFloor_cast_add_of_dvd
public import Theorems.Thm_QuadraticFloor_chi4_add
public import Theorems.Thm_QuadraticFloor_eta_add_half


set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {A : ℕ}
namespace QuadraticFloor
theorem _root_.solution (hp2 : p ≠ 2) (hA : Odd A) (ψ : DirichletCharacter ℂ A) (x : ℕ) :
    vartheta p ψ (x + 4 * A * p) = -vartheta p ψ x := by
  unfold vartheta
  rw [eta_add_half hp2 hA, chi4_add, cast_add_of_dvd x _ A ⟨4 * p, by ring⟩]
  push_cast; ring
end QuadraticFloor

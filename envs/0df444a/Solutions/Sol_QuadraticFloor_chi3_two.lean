-- Prove2me | solution 1 for QuadraticFloor.chi3_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:53:00.632421+00:00
-- url     : https://prove2.me/submissions/f8259259-ba60-4c88-84ae-765826a13503

module
public import Definitions.Def_QuadraticFloor_SquareClass
public import Definitions.Def_QuadraticFloor_Corollaries
public import Theorems.Thm_QuadraticFloor_chi3_apply

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuadraticFloor
theorem _root_.solution : chi3 2 = -1 := by
  have := chi3_apply 2
  rw [show legendreSym 3 ((2 : ℕ) : ℤ) = -1 by
    rw [legendreSym.mod]; decide] at this
  simpa using this
end QuadraticFloor

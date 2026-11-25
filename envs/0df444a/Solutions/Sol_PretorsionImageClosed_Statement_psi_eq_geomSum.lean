-- Prove2me | solution 1 for PretorsionImageClosed.Statement.psi_eq_geomSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:27:34.788866+00:00
-- url     : https://prove2.me/submissions/99f6009b-62b6-45c8-ad2d-8b02a1b95bf4

module
public import Definitions.Def_PretorsionImageClosed_Gandhi_Delta
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Definitions.Def_PretorsionImageClosed_Gandhi_ColumnSum
public import Theorems.Thm_PretorsionImageClosed_Statement_psi_empty
public import Theorems.Thm_PretorsionImageClosed_Statement_psi_insert_max

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed PretorsionImageClosed.Statement
open Polynomial Finset
variable {ι : Type*} [LinearOrder ι]
namespace PretorsionImageClosed.Statement
theorem _root_.solution (R : Finset ι) : psi R = geomSum R.card := by
  induction R using Finset.induction_on_max with
  | empty => rw [psi_empty, Finset.card_empty, geomSum_zero]
  | insert r R hr ih =>
    have hrR : r ∉ R := fun h => lt_irrefl r (hr r h)
    rw [psi_insert_max hr, ih, Finset.card_insert_of_notMem hrR, geomSum_succ]
end PretorsionImageClosed.Statement

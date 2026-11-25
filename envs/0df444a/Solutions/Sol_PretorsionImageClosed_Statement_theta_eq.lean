-- Prove2me | solution 1 for PretorsionImageClosed.Statement.theta_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:38:06.007897+00:00
-- url     : https://prove2.me/submissions/f68b03d1-487e-4c58-a56f-b346d5f47ccc

module
public import Definitions.Def_PretorsionImageClosed_Gandhi_Delta
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Definitions.Def_PretorsionImageClosed_Gandhi_ColumnSum
public import Theorems.Thm_PretorsionImageClosed_Statement_theta_empty
public import Theorems.Thm_PretorsionImageClosed_Statement_theta_insert_max
public import Theorems.Thm_PretorsionImageClosed_Statement_deltaXPow_succ_succ


set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed PretorsionImageClosed.Statement
open Polynomial Finset
variable {ι : Type*} [LinearOrder ι]
namespace PretorsionImageClosed.Statement
theorem _root_.solution (R : Finset ι) : theta R = X ^ (R.card + 1) + C q * X ^ 2 * deltaXPow R.card := by
  induction R using Finset.induction_on_max with
  | empty => rw [theta_empty]; simp [deltaXPow]
  | insert r R hr ih =>
    have hrR : r ∉ R := fun h => lt_irrefl r (hr r h)
    rw [theta_insert_max hr, ih, Finset.card_insert_of_notMem hrR]
    cases hR : R.card with
    | zero => simp [deltaXPow, geomSum_zero]; ring
    | succ m =>
      rw [deltaXPow_succ_succ]
      ring
end PretorsionImageClosed.Statement

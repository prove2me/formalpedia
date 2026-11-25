-- Prove2me | solution 1 for PretorsionImageClosed.Statement.psi_insert_max
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:24:18.972159+00:00
-- url     : https://prove2.me/submissions/81b79288-9180-483f-9bfe-9e46312110ec

module
public import Definitions.Def_PretorsionImageClosed_Gandhi_Delta
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Definitions.Def_PretorsionImageClosed_Gandhi_ColumnSum
public import Theorems.Thm_PretorsionImageClosed_Statement_psiTerm_insert_of_subset
public import Theorems.Thm_PretorsionImageClosed_Statement_psiTerm_insert_insert

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed PretorsionImageClosed.Statement
open Polynomial Finset
variable {ι : Type*} [LinearOrder ι]
namespace PretorsionImageClosed.Statement
theorem _root_.solution {r : ι} {R : Finset ι} (hr : ∀ x ∈ R, x < r) :
    psi (insert r R) = U * psi R + X ^ (R.card + 1) := by
  have hrR : r ∉ R := fun h => lt_irrefl r (hr r h)
  unfold psi
  rw [Finset.sum_powerset_insert hrR]
  rw [Finset.sum_congr rfl (fun Cont hCont =>
    psiTerm_insert_of_subset hr (Finset.mem_powerset.1 hCont))]
  rw [Finset.sum_congr rfl (fun Cont hCont =>
    psiTerm_insert_insert hr (Finset.mem_powerset.1 hCont))]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq'
    R.powerset R (fun _ => X ^ R.card), if_pos (Finset.mem_powerset.2 (Finset.Subset.refl _))]
  ring
end PretorsionImageClosed.Statement

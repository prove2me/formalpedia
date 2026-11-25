-- Prove2me | solution 1 for PretorsionImageClosed.Statement.theta_insert_max
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:27:31.203037+00:00
-- url     : https://prove2.me/submissions/0733491f-484f-40de-8c43-b4cfb3536961

module
public import Definitions.Def_PretorsionImageClosed_Gandhi_Delta
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Definitions.Def_PretorsionImageClosed_Gandhi_ColumnSum
public import Theorems.Thm_PretorsionImageClosed_Statement_thetaTerm_insert_of_subset
public import Theorems.Thm_PretorsionImageClosed_Statement_thetaTerm_insert_insert

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
    theta (insert r R) = U * theta R + (X - 1) * X ^ (R.card + 1) := by
  have hrR : r ∉ R := fun h => lt_irrefl r (hr r h)
  unfold theta
  rw [Finset.sum_powerset_insert hrR]
  rw [Finset.sum_congr rfl (fun J hJ => thetaTerm_insert_of_subset hr (Finset.mem_powerset.1 hJ))]
  rw [Finset.sum_congr rfl (fun J hJ => thetaTerm_insert_insert hr (Finset.mem_powerset.1 hJ))]
  rw [← Finset.mul_sum]
  have hsplit : ∑ J ∈ R.powerset, thetaTerm R J * (if J = ∅ then X else 1) =
      ∑ J ∈ R.powerset, thetaTerm R J + (X - 1) * thetaTerm R ∅ := by
    rw [Finset.sum_congr rfl (fun J _ => show thetaTerm R J * (if J = ∅ then X else 1) =
      thetaTerm R J + (if J = ∅ then (X - 1) * thetaTerm R J else 0) by split_ifs <;> ring)]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq' R.powerset ∅,
      if_pos (Finset.mem_powerset.2 (Finset.empty_subset _))]
  rw [hsplit]
  have h0 : thetaTerm R ∅ = X ^ (R.card + 1) := by
    simp [thetaTerm, admCount]
  rw [h0]
  ring
end PretorsionImageClosed.Statement

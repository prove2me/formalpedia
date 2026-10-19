-- Prove2me | solution 1 for PermanentRollout.coeff_columnLinearFormProduct_eq_permanent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:07.661825+00:00
-- url     : https://prove2.me/submissions/399b9cab-f6ad-487a-99db-0b25d38b29a3

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_coeff_columnLinearFormProduct_eq_assignment_sum
import Theorems.Thm_PermanentRollout_columnAssignmentExponent_equiv_apply

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution {r k : ℕ}
    (U : Matrix (Fin r) (Fin k) ℂ) (rows : Finset (Fin r))
    (rowEquiv : Fin k ≃ {row // row ∈ rows}) :
    MvPolynomial.coeff (squareFreeExponent rows)
      (columnLinearFormProduct U) =
        Matrix.permanent
          (fun i j : Fin k => U (rowEquiv i).val j) := by
  classical
  rw [coeff_columnLinearFormProduct_eq_assignment_sum]
  unfold Matrix.permanent
  rw [← Finset.sum_filter]
  refine Finset.sum_bij
    (fun assignment hassignment =>
      squareFreeColumnMatchingPermutation rows rowEquiv assignment
        (Finset.mem_filter.mp hassignment).2)
    (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro left hleft right hright hmatch
    funext column
    have hvalues := congrArg
      (fun permutation : Equiv.Perm (Fin k) =>
        (rowEquiv (permutation column)).val) hmatch
    simpa only [squareFreeColumnMatchingPermutation_apply] using hvalues
  · intro permutation _
    let assignment : Fin k → Fin r :=
      fun column => (rowEquiv (permutation column)).val
    have hassignment : columnAssignmentExponent assignment =
        squareFreeExponent rows :=
      columnAssignmentExponent_equiv_apply rows rowEquiv permutation
    refine ⟨assignment,
      Finset.mem_filter.mpr ⟨Finset.mem_univ assignment, hassignment⟩, ?_⟩
    apply Equiv.ext
    intro column
    apply rowEquiv.injective
    apply Subtype.ext
    simpa only [squareFreeColumnMatchingPermutation_apply] using
      (show assignment column =
        (rowEquiv (permutation column)).val from rfl)
  · intro assignment hassignment
    apply Finset.prod_congr rfl
    intro column _
    change U (assignment column) column =
      U (rowEquiv
        (squareFreeColumnMatchingPermutation rows rowEquiv assignment
          (Finset.mem_filter.mp hassignment).2 column)).val column
    rw [squareFreeColumnMatchingPermutation_apply]
end PermanentRollout

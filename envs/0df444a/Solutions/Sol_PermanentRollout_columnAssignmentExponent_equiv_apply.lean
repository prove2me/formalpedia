-- Prove2me | solution 1 for PermanentRollout.columnAssignmentExponent_equiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:07.661825+00:00
-- url     : https://prove2.me/submissions/d205b040-45d8-43d9-8503-046968428c5e

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution {r k : ℕ}
    (rows : Finset (Fin r)) (rowEquiv : Fin k ≃ {row // row ∈ rows})
    (permutation : Equiv.Perm (Fin k)) :
    columnAssignmentExponent
      (fun column => (rowEquiv (permutation column)).val) =
        squareFreeExponent rows := by
  classical
  ext row
  rw [columnAssignmentExponent_apply, squareFreeExponent_apply]
  by_cases hrow : row ∈ rows
  · have hfiber :
        ((Finset.univ : Finset (Fin k)).filter
          (fun column => (rowEquiv (permutation column)).val = row)) =
            {permutation.symm (rowEquiv.symm ⟨row, hrow⟩)} := by
      ext column
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      constructor
      · intro hcolumn
        have hsubtype : rowEquiv (permutation column) =
            (⟨row, hrow⟩ : {row // row ∈ rows}) :=
          Subtype.ext hcolumn
        calc
          column = permutation.symm (permutation column) :=
            (permutation.symm_apply_apply column).symm
          _ = permutation.symm (rowEquiv.symm ⟨row, hrow⟩) := by
            simpa using congrArg
              (fun selected : {row // row ∈ rows} =>
                permutation.symm (rowEquiv.symm selected)) hsubtype
      · intro hcolumn
        subst column
        simp
    simp [hfiber, hrow]
  · have hfiber :
        ((Finset.univ : Finset (Fin k)).filter
          (fun column => (rowEquiv (permutation column)).val = row)) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro column hcolumn
      have hvalue := (Finset.mem_filter.mp hcolumn).2
      apply hrow
      rw [← hvalue]
      exact (rowEquiv (permutation column)).property
    simp [hfiber, hrow]
end PermanentRollout

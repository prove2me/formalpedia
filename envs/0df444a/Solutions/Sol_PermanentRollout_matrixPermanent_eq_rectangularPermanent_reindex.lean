-- Prove2me | solution 1 for PermanentRollout.matrixPermanent_eq_rectangularPermanent_reindex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:10.343013+00:00
-- url     : https://prove2.me/submissions/ddae55fb-6d6b-4b86-a0f6-ecee89f15c6f

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section
namespace PermanentRollout
theorem _root_.solution
    {n : ℕ} {α β R : Type*}
    [Fintype α] [Fintype β] [CommSemiring R]
    (row : Fin n ≃ α) (column : Fin n ≃ β)
    (A : Matrix α β R) :
    Matrix.permanent (fun i j : Fin n => A (row i) (column j)) =
      rectangularPermanent A := by
  classical
  unfold Matrix.permanent rectangularPermanent
  let matchingEquiv : Equiv.Perm (Fin n) ≃ (α ≃ β) :=
    { toFun := fun σ => row.symm.trans (σ.symm.trans column)
      invFun := fun matching =>
        (row.trans (matching.trans column.symm)).symm
      left_inv := by
        intro σ
        ext i
        simp
      right_inv := by
        intro matching
        ext i
        simp }
  refine Fintype.sum_equiv matchingEquiv _ _ ?_
  intro σ
  refine Fintype.prod_equiv (σ.trans row) _ _ ?_
  intro i
  simp [matchingEquiv]
end PermanentRollout

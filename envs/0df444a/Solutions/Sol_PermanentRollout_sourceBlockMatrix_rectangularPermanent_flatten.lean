-- Prove2me | solution 1 for PermanentRollout.sourceBlockMatrix_rectangularPermanent_flatten
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:10.343013+00:00
-- url     : https://prove2.me/submissions/bd9201cc-9938-4f84-a52e-81cbb4031c6b

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
    (r s d : ℕ) (U : Matrix (Fin r) (Fin (r - d)) ℂ) :
    rectangularPermanent
        (sourceBlockMatrix r s d
          (fun i j =>
            (MvPolynomial.X
              ((finProdFinEquiv : Fin r × Fin s ≃ Fin (r * s))
                (i, j)) : MvPolynomial (Fin (r * s)) ℂ))
          (fun i j =>
            algebraMap ℂ (MvPolynomial (Fin (r * s)) ℂ) (U i j))) =
      MvPolynomial.rename
        (finProdFinEquiv : Fin r × Fin s ≃ Fin (r * s))
        (rectangularPermanent
          (sourceBlockMatrix r s d
            (fun i j =>
              (MvPolynomial.X (i, j) :
                MvPolynomial (Fin r × Fin s) ℂ))
            (fun i j =>
              algebraMap ℂ (MvPolynomial (Fin r × Fin s) ℂ)
                (U i j)))) := by
  classical
  simp only [rectangularPermanent, map_sum, map_prod]
  apply Finset.sum_congr rfl
  intro matching _
  apply Finset.prod_congr rfl
  intro row _
  cases row with
  | inl i =>
      cases hcolumn : matching (.inl i) <;>
        simp [sourceBlockMatrix, Matrix.fromBlocks]
  | inr i =>
      cases hcolumn : matching (.inr i) <;>
        simp [sourceBlockMatrix, Matrix.fromBlocks]
end PermanentRollout

-- Prove2me | solution 1 for PermanentRollout.blockMinorGraphPullback_rename_matrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:10.343013+00:00
-- url     : https://prove2.me/submissions/ba67a8cf-1972-4019-bd6c-0390a04e6ae0

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
    (b t s : ℕ) (f : MvPolynomial (Fin (b * t) × Fin s) ℂ) :
    blockMinorGraphPullback b t s
        (MvPolynomial.rename
          (blockMinorMatrixCoordinateLift b t s) f) = f := by
  classical
  induction f using MvPolynomial.induction_on with
  | C c => simp [blockMinorGraphPullback]
  | add f g hf hg => simp [map_add, hf, hg]
  | mul_X f coordinate hf =>
      rw [map_mul, map_mul, hf]
      have hcoordinate :
          sourceRowBlockVariableEmbedding b t s
              (((finProdFinEquiv : Fin b × Fin t ≃ Fin (b * t)).symm
                coordinate.1).1)
              (((finProdFinEquiv : Fin b × Fin t ≃ Fin (b * t)).symm
                coordinate.1).2, coordinate.2) = coordinate := by
        apply Prod.ext
        · change
            (finProdFinEquiv : Fin b × Fin t ≃ Fin (b * t))
              ((finProdFinEquiv : Fin b × Fin t ≃ Fin (b * t)).symm
                coordinate.1) = coordinate.1
          exact Equiv.apply_symm_apply _ _
        · rfl
      rw [MvPolynomial.rename_X]
      simp only [blockMinorGraphPullback,
        MvPolynomial.aeval_X, blockMinorMatrixCoordinateLift]
      change f * MvPolynomial.X
        (sourceRowBlockVariableEmbedding b t s
          (((finProdFinEquiv : Fin b × Fin t ≃ Fin (b * t)).symm
            coordinate.1).1)
          (((finProdFinEquiv : Fin b × Fin t ≃ Fin (b * t)).symm
            coordinate.1).2, coordinate.2)) =
          f * MvPolynomial.X coordinate
      rw [hcoordinate]
end PermanentRollout

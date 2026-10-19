-- Prove2me | solution 1 for PermanentRollout.sourceBlock_affine_permanent_specialization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:10.343013+00:00
-- url     : https://prove2.me/submissions/75aa8ca9-1d3b-49a5-a81d-d2cc7bfcd0aa

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_permanent_aeval_eq_matrix_permanent
import Theorems.Thm_PermanentRollout_matrixPermanent_eq_rectangularPermanent_reindex
import Theorems.Thm_PermanentRollout_sourceBlockAffineInput_polynomial

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section
namespace PermanentRollout
theorem _root_.solution
    {n r s d : ℕ}
    (rowEquiv : Fin n ≃ Fin r ⊕ Fin (s - d))
    (columnEquiv : Fin n ≃ Fin s ⊕ Fin (r - d))
    (U : Matrix (Fin r) (Fin (r - d)) ℂ) :
    MvPolynomial.aeval
        (fun ij : Fin n × Fin n =>
          (sourceBlockAffineInput U
            (rowEquiv ij.1) (columnEquiv ij.2)).polynomial)
        (permanent n) =
      rectangularPermanent
        (sourceBlockMatrix r s d
          (fun i j =>
            MvPolynomial.X
              ((finProdFinEquiv : Fin r × Fin s ≃ Fin (r * s))
                (i, j)))
          (fun i j =>
            algebraMap ℂ (MvPolynomial (Fin (r * s)) ℂ)
              (U i j))) := by
  let B : Matrix (Fin r ⊕ Fin (s - d))
      (Fin s ⊕ Fin (r - d))
      (MvPolynomial (Fin (r * s)) ℂ) :=
    sourceBlockMatrix r s d
      (fun i j =>
        MvPolynomial.X
          ((finProdFinEquiv : Fin r × Fin s ≃ Fin (r * s))
            (i, j)))
      (fun i j =>
        algebraMap ℂ (MvPolynomial (Fin (r * s)) ℂ) (U i j))
  have hentry (i j : Fin n) :
      (sourceBlockAffineInput U (rowEquiv i) (columnEquiv j)).polynomial =
        B (rowEquiv i) (columnEquiv j) :=
    sourceBlockAffineInput_polynomial U (rowEquiv i) (columnEquiv j)
  calc
    MvPolynomial.aeval
        (fun ij : Fin n × Fin n =>
          (sourceBlockAffineInput U
            (rowEquiv ij.1) (columnEquiv ij.2)).polynomial)
        (permanent n) =
      Matrix.permanent
        (fun i j => B (rowEquiv i) (columnEquiv j)) := by
          rw [show
            (fun ij : Fin n × Fin n =>
              (sourceBlockAffineInput U
                (rowEquiv ij.1) (columnEquiv ij.2)).polynomial) =
              (fun ij : Fin n × Fin n =>
                B (rowEquiv ij.1) (columnEquiv ij.2)) by
                  funext ij
                  exact hentry ij.1 ij.2]
          exact permanent_aeval_eq_matrix_permanent
            (fun i j => B (rowEquiv i) (columnEquiv j))
    _ = rectangularPermanent B :=
      matrixPermanent_eq_rectangularPermanent_reindex
        rowEquiv columnEquiv B
end PermanentRollout

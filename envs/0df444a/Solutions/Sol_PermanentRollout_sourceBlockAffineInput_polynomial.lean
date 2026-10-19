-- Prove2me | solution 1 for PermanentRollout.sourceBlockAffineInput_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:10.343013+00:00
-- url     : https://prove2.me/submissions/08e8be60-c839-4ad7-a572-1a4d307a4da2

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
    {r s d : ℕ}
    (U : Matrix (Fin r) (Fin (r - d)) ℂ)
    (row : Fin r ⊕ Fin (s - d))
    (column : Fin s ⊕ Fin (r - d)) :
    (sourceBlockAffineInput U row column).polynomial =
      sourceBlockMatrix r s d
        (fun i j =>
          MvPolynomial.X
            ((finProdFinEquiv : Fin r × Fin s ≃ Fin (r * s))
              (i, j)))
        (fun i j =>
          algebraMap ℂ (MvPolynomial (Fin (r * s)) ℂ) (U i j))
        row column := by
  cases row <;> cases column <;>
    simp [sourceBlockAffineInput, FreeAffineInput.polynomial,
      sourceBlockMatrix, Matrix.fromBlocks]
end PermanentRollout

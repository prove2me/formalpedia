-- Prove2me | solution 1 for PermanentFormulaLowerBound.matchingWeightedBivariateEvaluationMatrix_eq_diagonal_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.22648+00:00
-- url     : https://prove2.me/submissions/bdeab9d0-3455-4db6-be93-092c39e9a05a

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution
    {F : Type*} [CommRing F] {ell m : ℕ}
    (p q : Fin m → F)
    (P Q : Fin m → Finset (Fin ell)) :
    matchingWeightedBivariateEvaluationMatrix p q P Q =
      Matrix.diagonal
        (fun de : Fin m × Fin m =>
          (matchingJacobianWeight m (P de.1).card (Q de.2).card : F)) *
        matchingBivariateEvaluationMatrix p q P Q := by
  ext de ab
  rw [Matrix.diagonal_mul]
  rfl
end PermanentFormulaLowerBound

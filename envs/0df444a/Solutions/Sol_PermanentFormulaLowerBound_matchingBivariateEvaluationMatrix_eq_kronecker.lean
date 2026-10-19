-- Prove2me | solution 1 for PermanentFormulaLowerBound.matchingBivariateEvaluationMatrix_eq_kronecker
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.22648+00:00
-- url     : https://prove2.me/submissions/796ac042-04d8-43cd-a84a-d9e12ec35091

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
    matchingBivariateEvaluationMatrix p q P Q =
      ((matchingPolynomialEvaluationMatrix p P)ᵀ ⊗ₖ
        (matchingPolynomialEvaluationMatrix q Q)ᵀ).submatrix
          id (Equiv.prodComm (Fin m) (Fin m)) := by
  ext ⟨d, e⟩ ⟨a, b⟩
  rfl
end PermanentFormulaLowerBound

-- Prove2me | solution 1 for PermanentFormulaLowerBound.matchingMarkedPermanent_bit_coefficients_algebraicIndependent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.787743+00:00
-- url     : https://prove2.me/submissions/3802d1fe-4e03-4d7f-8d76-5033e8d09aa2

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_algebraicIndependent_of_evaluatedJacobianMinor_det_ne_zero
import Theorems.Thm_PermanentFormulaLowerBound_matchingPermanentJacobian_det_ne_zero

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution
    {ell m : ℕ} (p q : Fin m → ℂ)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hm : m ≤ 2 ^ ell) (hroom : 2 * ell < m) :
    AlgebraicIndependent ℂ
      (fun de : Fin m × Fin m =>
        coefficientPolynomial
          (matchingMarkedPermanent (matchingDiagonalEmbedding ell m))
          (matchingSquarefreeMonomial
            (matchingBitCoefficientSet ell m de))) := by
  apply algebraicIndependent_of_evaluatedJacobianMinor_det_ne_zero
    (fun de : Fin m × Fin m =>
      coefficientPolynomial
        (matchingMarkedPermanent (matchingDiagonalEmbedding ell m))
        (matchingSquarefreeMonomial
          (matchingBitCoefficientSet ell m de)))
    (fun ab : Fin m × Fin m =>
      matchingExternalEntry ell m ab.1 ab.2)
    (matchingPermanentSpecialization p q)
  exact matchingPermanentJacobian_det_ne_zero p q hp hq hm hroom
end PermanentFormulaLowerBound

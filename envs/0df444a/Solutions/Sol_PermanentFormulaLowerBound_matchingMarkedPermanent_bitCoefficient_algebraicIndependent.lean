-- Prove2me | solution 1 for PermanentFormulaLowerBound.matchingMarkedPermanent_bitCoefficient_algebraicIndependent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.787743+00:00
-- url     : https://prove2.me/submissions/77af50f9-58a6-4391-a674-54a4112ccbc7

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_matchingMarkedPermanent_bit_coefficients_algebraicIndependent
import Theorems.Thm_PermanentFormulaLowerBound_matchingCanonicalComplexPoints_injective

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution
    {ell m : ℕ} (hm : m ≤ 2 ^ ell) (hroom : 2 * ell < m) :
    AlgebraicIndependent ℂ
      (fun de : Fin m × Fin m =>
        coefficientPolynomial
          (matchingMarkedPermanent (matchingDiagonalEmbedding ell m))
          (matchingSquarefreeMonomial
            (matchingBitCoefficientSet ell m de))) :=
  matchingMarkedPermanent_bit_coefficients_algebraicIndependent
    (matchingCanonicalComplexPoints m)
    (matchingCanonicalComplexPoints m)
    (matchingCanonicalComplexPoints_injective m)
    (matchingCanonicalComplexPoints_injective m)
    hm hroom
end PermanentFormulaLowerBound

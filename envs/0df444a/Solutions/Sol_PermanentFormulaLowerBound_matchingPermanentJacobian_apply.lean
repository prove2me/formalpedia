-- Prove2me | solution 1 for PermanentFormulaLowerBound.matchingPermanentJacobian_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.22648+00:00
-- url     : https://prove2.me/submissions/0568c0c4-f6f3-416a-9d22-2f0e3492acdb

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_matchingMarkedPermanent_evaluated_coefficient_pderiv_eq_row_sum

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution
    {ell m : ℕ} (p q : Fin m → ℂ)
    (de ab : Fin m × Fin m) :
    matchingPermanentJacobian (ell := ell) p q de ab =
      ∑ σ : Equiv.Perm (Fin ((ell + ell) + m)),
        if matchingPermutationExponent
          (matchingDiagonalEmbedding ell m) σ =
              matchingSquarefreeMonomial
                (matchingBitCoefficientSet ell m de) ∧
          σ (matchingExternalEntry ell m ab.1 ab.2).1.1 =
            (matchingExternalEntry ell m ab.1 ab.2).1.2 then
          ∏ i : {i : Fin ((ell + ell) + m) //
            i ≠ (matchingExternalEntry ell m ab.1 ab.2).1.1},
            MvPolynomial.eval (matchingPermanentSpecialization p q)
              (matchingPermutationOutsideFactor
                (matchingDiagonalEmbedding ell m) σ i.1)
        else 0 := by
  classical
  unfold matchingPermanentJacobian evaluatedJacobianMinor
  exact matchingMarkedPermanent_evaluated_coefficient_pderiv_eq_row_sum
    (matchingDiagonalEmbedding ell m)
    (matchingSquarefreeMonomial
      (matchingBitCoefficientSet ell m de))
    (matchingExternalEntry ell m ab.1 ab.2)
    (matchingPermanentSpecialization p q)
end PermanentFormulaLowerBound

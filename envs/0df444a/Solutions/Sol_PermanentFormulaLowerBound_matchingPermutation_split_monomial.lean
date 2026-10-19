-- Prove2me | solution 1 for PermanentFormulaLowerBound.matchingPermutation_split_monomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:12.090475+00:00
-- url     : https://prove2.me/submissions/674ebcaa-0e32-475c-92af-e782705aec1b

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
    {n : ℕ} {Y : Type u} (d : Y ↪ Fin n × Fin n)
    (σ : Equiv.Perm (Fin n)) :
    MvPolynomial.sumAlgEquiv ℂ Y (matchingOutside d)
        (MvPolynomial.renameEquiv ℂ (matchingVariableEquiv d).symm
          (∏ i : Fin n,
            (MvPolynomial.X (i, σ i) :
              MvPolynomial (Fin n × Fin n) ℂ))) =
      MvPolynomial.monomial (matchingPermutationExponent d σ)
        (matchingPermutationOutsideProduct d σ) := by
  classical
  unfold matchingPermutationExponent matchingPermutationOutsideProduct
  rw [map_prod, map_prod]
  rw [MvPolynomial.monomial_sum_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X]
  cases h : (matchingVariableEquiv d).symm (i, σ i) with
  | inl y =>
      simp [MvPolynomial.sumAlgEquiv_X_inl,
        ← MvPolynomial.C_mul_X_eq_monomial]
  | inr z =>
      simp [MvPolynomial.sumAlgEquiv_X_inr]
end PermanentFormulaLowerBound

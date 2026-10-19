-- Prove2me | solution 1 for PermanentFormulaLowerBound.matchingPermutationOutsideFactor_internal_product_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:12.090475+00:00
-- url     : https://prove2.me/submissions/f96a272c-f9bb-433e-90dd-0d0dcad60952

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_matchingPermutationOutsideFactor_internal_offDiagonal_eval

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution
    {ell m : ℕ} (p q : Fin m → ℂ)
    (σ : Equiv.Perm (Fin ((ell + ell) + m)))
    (a b : Fin m) (y y' : Fin ell ⊕ Fin ell) (hne : y' ≠ y)
    (hσ : σ (matchingBlockIndexEquiv ell m (.inl y)) =
      matchingBlockIndexEquiv ell m (.inl y')) :
    (∏ i : {i : Fin ((ell + ell) + m) //
        i ≠ (matchingExternalEntry ell m a b).1.1},
      MvPolynomial.eval (matchingPermanentSpecialization p q)
        (matchingPermutationOutsideFactor
          (matchingDiagonalEmbedding ell m) σ i.1)) = 0 := by
  classical
  have hnot :
      matchingBlockIndexEquiv ell m (.inl y) ≠
        (matchingExternalEntry ell m a b).1.1 := by
    intro h
    have hsum :
        (Sum.inl y : (Fin ell ⊕ Fin ell) ⊕ Fin m) = .inr a := by
      apply (matchingBlockIndexEquiv ell m).injective
      change
        matchingBlockIndexEquiv ell m (.inl y) =
          matchingBlockIndexEquiv ell m (.inr a) at h
      exact h
    cases hsum
  let i : {i : Fin ((ell + ell) + m) //
      i ≠ (matchingExternalEntry ell m a b).1.1} :=
    ⟨matchingBlockIndexEquiv ell m (.inl y), hnot⟩
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  exact matchingPermutationOutsideFactor_internal_offDiagonal_eval
    p q σ y y' hne hσ
end PermanentFormulaLowerBound

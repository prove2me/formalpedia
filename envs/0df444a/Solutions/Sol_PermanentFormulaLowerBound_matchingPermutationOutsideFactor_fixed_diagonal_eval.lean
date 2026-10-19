-- Prove2me | solution 1 for PermanentFormulaLowerBound.matchingPermutationOutsideFactor_fixed_diagonal_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:12.090475+00:00
-- url     : https://prove2.me/submissions/34e6a717-1d38-46c3-9bf6-3b59f7cb56a9

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
    {ell m : ℕ} (p q : Fin m → ℂ)
    (σ : Equiv.Perm (Fin ((ell + ell) + m)))
    (y : Fin ell ⊕ Fin ell)
    (hσ : σ (matchingBlockIndexEquiv ell m (.inl y)) =
      matchingBlockIndexEquiv ell m (.inl y)) :
    MvPolynomial.eval (matchingPermanentSpecialization p q)
      (matchingPermutationOutsideFactor (matchingDiagonalEmbedding ell m)
        σ (matchingBlockIndexEquiv ell m (.inl y))) = 1 := by
  classical
  have hsplit :
      (matchingVariableEquiv (matchingDiagonalEmbedding ell m)).symm
        (matchingBlockIndexEquiv ell m (.inl y),
          matchingBlockIndexEquiv ell m (.inl y)) = .inl y := by
    apply (matchingVariableEquiv
      (matchingDiagonalEmbedding ell m)).injective
    simp only [Equiv.apply_symm_apply]
    rfl
  unfold matchingPermutationOutsideFactor
  rw [hσ, hsplit]
  simp
end PermanentFormulaLowerBound

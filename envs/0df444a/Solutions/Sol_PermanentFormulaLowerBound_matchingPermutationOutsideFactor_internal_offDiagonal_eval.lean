-- Prove2me | solution 1 for PermanentFormulaLowerBound.matchingPermutationOutsideFactor_internal_offDiagonal_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:12.090475+00:00
-- url     : https://prove2.me/submissions/3e55ee8d-2ad3-4332-955d-aa2e525a4835

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
    (y y' : Fin ell ⊕ Fin ell) (hne : y' ≠ y)
    (hσ : σ (matchingBlockIndexEquiv ell m (.inl y)) =
      matchingBlockIndexEquiv ell m (.inl y')) :
    MvPolynomial.eval (matchingPermanentSpecialization p q)
      (matchingPermutationOutsideFactor
        (matchingDiagonalEmbedding ell m) σ
        (matchingBlockIndexEquiv ell m (.inl y))) = 0 := by
  classical
  let z : matchingOutside (matchingDiagonalEmbedding ell m) :=
    ⟨(matchingBlockIndexEquiv ell m (.inl y),
      matchingBlockIndexEquiv ell m (.inl y')), by
      rintro ⟨t, ht⟩
      have hrow := congrArg Prod.fst ht
      change
        matchingBlockIndexEquiv ell m (.inl t) =
          matchingBlockIndexEquiv ell m (.inl y) at hrow
      have hcol := congrArg Prod.snd ht
      change
        matchingBlockIndexEquiv ell m (.inl t) =
          matchingBlockIndexEquiv ell m (.inl y') at hcol
      have hty : t = y :=
        Sum.inl_injective ((matchingBlockIndexEquiv ell m).injective hrow)
      have hty' : t = y' :=
        Sum.inl_injective ((matchingBlockIndexEquiv ell m).injective hcol)
      exact hne (hty'.symm.trans hty)⟩
  have hsplit :
      (matchingVariableEquiv (matchingDiagonalEmbedding ell m)).symm
        (matchingBlockIndexEquiv ell m (.inl y),
          matchingBlockIndexEquiv ell m (.inl y')) = .inr z := by
    apply (matchingVariableEquiv (matchingDiagonalEmbedding ell m)).injective
    simp [z]
  unfold matchingPermutationOutsideFactor
  rw [hσ, hsplit]
  simp [matchingPermanentSpecialization, z]
end PermanentFormulaLowerBound

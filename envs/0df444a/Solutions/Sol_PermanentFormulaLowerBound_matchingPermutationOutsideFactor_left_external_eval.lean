-- Prove2me | solution 1 for PermanentFormulaLowerBound.matchingPermutationOutsideFactor_left_external_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:12.090475+00:00
-- url     : https://prove2.me/submissions/b7abecd1-f0f1-4510-ba96-704040cf418d

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_matchingPermutationOutsideFactor_eval_of_not_mem_range
import Theorems.Thm_PermanentFormulaLowerBound_matching_internal_external_not_mem_diagonal

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
    (u : Fin ell) (b : Fin m)
    (hσ : σ (matchingBlockIndexEquiv ell m (.inl (.inl u))) =
      matchingBlockIndexEquiv ell m (.inr b)) :
    MvPolynomial.eval (matchingPermanentSpecialization p q)
      (matchingPermutationOutsideFactor (matchingDiagonalEmbedding ell m)
        σ (matchingBlockIndexEquiv ell m (.inl (.inl u)))) =
      p b ^ (2 ^ (u : ℕ)) := by
  rw [matchingPermutationOutsideFactor_eval_of_not_mem_range
    (matchingDiagonalEmbedding ell m) σ
    (matchingBlockIndexEquiv ell m (.inl (.inl u)))
    (matchingBlockIndexEquiv ell m (.inr b)) hσ
    (matching_internal_external_not_mem_diagonal (.inl u) b)]
  simp [matchingPermanentSpecialization]
end PermanentFormulaLowerBound

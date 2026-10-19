-- Prove2me | solution 1 for PermanentFormulaLowerBound.matchingPermutationOutsideFactor_external_external_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:12.090475+00:00
-- url     : https://prove2.me/submissions/cf251afd-d549-4b3f-ad20-3ea9ada5d494

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_matchingPermutationOutsideFactor_eval_of_not_mem_range
import Theorems.Thm_PermanentFormulaLowerBound_matching_external_external_not_mem_diagonal

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
    (a b : Fin m)
    (hσ : σ (matchingBlockIndexEquiv ell m (.inr a)) =
      matchingBlockIndexEquiv ell m (.inr b)) :
    MvPolynomial.eval (matchingPermanentSpecialization p q)
      (matchingPermutationOutsideFactor (matchingDiagonalEmbedding ell m)
        σ (matchingBlockIndexEquiv ell m (.inr a))) = 1 := by
  rw [matchingPermutationOutsideFactor_eval_of_not_mem_range
    (matchingDiagonalEmbedding ell m) σ
    (matchingBlockIndexEquiv ell m (.inr a))
    (matchingBlockIndexEquiv ell m (.inr b)) hσ
    (matching_external_external_not_mem_diagonal a b)]
  simp [matchingPermanentSpecialization]
end PermanentFormulaLowerBound

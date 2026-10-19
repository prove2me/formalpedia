-- Prove2me | solution 1 for PermanentFormulaLowerBound.matchingPermutationOutsideFactor_external_right_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:12.090475+00:00
-- url     : https://prove2.me/submissions/061490d6-e481-4c53-9471-7e4a97663dfc

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_matchingPermutationOutsideFactor_eval_of_not_mem_range
import Theorems.Thm_PermanentFormulaLowerBound_matching_external_internal_not_mem_diagonal

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
    (a : Fin m) (v : Fin ell)
    (hσ : σ (matchingBlockIndexEquiv ell m (.inr a)) =
      matchingBlockIndexEquiv ell m (.inl (.inr v))) :
    MvPolynomial.eval (matchingPermanentSpecialization p q)
      (matchingPermutationOutsideFactor (matchingDiagonalEmbedding ell m)
        σ (matchingBlockIndexEquiv ell m (.inr a))) =
      q a ^ (2 ^ (v : ℕ)) := by
  rw [matchingPermutationOutsideFactor_eval_of_not_mem_range
    (matchingDiagonalEmbedding ell m) σ
    (matchingBlockIndexEquiv ell m (.inr a))
    (matchingBlockIndexEquiv ell m (.inl (.inr v))) hσ
    (matching_external_internal_not_mem_diagonal a (.inr v))]
  simp [matchingPermanentSpecialization]
end PermanentFormulaLowerBound

-- Prove2me | solution 1 for PermanentFormulaLowerBound.matching_internal_external_not_mem_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:12.090475+00:00
-- url     : https://prove2.me/submissions/e81a651f-5002-4a98-ba2e-07269647eb9e

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
    {ell m : ℕ} (y : Fin ell ⊕ Fin ell) (b : Fin m) :
    (matchingBlockIndexEquiv ell m (.inl y),
      matchingBlockIndexEquiv ell m (.inr b)) ∉
        Set.range (matchingDiagonalEmbedding ell m) := by
  rintro ⟨t, ht⟩
  have hcol := congrArg Prod.snd ht
  change
    matchingBlockIndexEquiv ell m (.inl t) =
      matchingBlockIndexEquiv ell m (.inr b) at hcol
  cases (matchingBlockIndexEquiv ell m).injective hcol
end PermanentFormulaLowerBound

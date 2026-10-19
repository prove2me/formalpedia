-- Prove2me | solution 1 for PermanentFormulaLowerBound.matching_external_internal_not_mem_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:12.090475+00:00
-- url     : https://prove2.me/submissions/afe35ced-d7fc-40f7-9ab2-e955a386e18d

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
    {ell m : ℕ} (a : Fin m) (y : Fin ell ⊕ Fin ell) :
    (matchingBlockIndexEquiv ell m (.inr a),
      matchingBlockIndexEquiv ell m (.inl y)) ∉
        Set.range (matchingDiagonalEmbedding ell m) := by
  rintro ⟨t, ht⟩
  have hrow := congrArg Prod.fst ht
  change
    matchingBlockIndexEquiv ell m (.inl t) =
      matchingBlockIndexEquiv ell m (.inr a) at hrow
  cases (matchingBlockIndexEquiv ell m).injective hrow
end PermanentFormulaLowerBound

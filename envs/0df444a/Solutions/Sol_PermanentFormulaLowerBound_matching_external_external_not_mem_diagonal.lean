-- Prove2me | solution 1 for PermanentFormulaLowerBound.matching_external_external_not_mem_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:12.090475+00:00
-- url     : https://prove2.me/submissions/760871b3-ee0a-4c17-87a8-edd92a054f87

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
    {ell m : ℕ} (a b : Fin m) :
    (matchingBlockIndexEquiv ell m (.inr a),
      matchingBlockIndexEquiv ell m (.inr b)) ∉
        Set.range (matchingDiagonalEmbedding ell m) := by
  rintro ⟨t, ht⟩
  have hrow := congrArg Prod.fst ht
  change
    matchingBlockIndexEquiv ell m (.inl t) =
      matchingBlockIndexEquiv ell m (.inr a) at hrow
  cases (matchingBlockIndexEquiv ell m).injective hrow
end PermanentFormulaLowerBound

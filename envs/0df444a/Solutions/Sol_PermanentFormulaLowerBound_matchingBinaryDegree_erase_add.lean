-- Prove2me | solution 1 for PermanentFormulaLowerBound.matchingBinaryDegree_erase_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.22648+00:00
-- url     : https://prove2.me/submissions/c5499286-18ed-428c-b209-8b8f3b1e753a

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution {ell : ℕ}
    (P : Finset (Fin ell)) (u : Fin ell) (hu : u ∈ P) :
    matchingBinaryDegree (P.erase u) + 2 ^ (u : ℕ) = matchingBinaryDegree P := by
  classical
  unfold matchingBinaryDegree
  rw [← Finset.sum_erase_add _ _ hu]
end PermanentFormulaLowerBound

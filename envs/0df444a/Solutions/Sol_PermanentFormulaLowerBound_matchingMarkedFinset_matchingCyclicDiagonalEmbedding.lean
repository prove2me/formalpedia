-- Prove2me | solution 1 for PermanentFormulaLowerBound.matchingMarkedFinset_matchingCyclicDiagonalEmbedding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.787743+00:00
-- url     : https://prove2.me/submissions/3ea61641-a1fc-4891-9fc0-f9a5d7b4d553

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
    {n ell : ℕ} (hk : 0 < 2 * ell)
    (t : Fin n) (j : Fin (n / (2 * ell))) :
    matchingMarkedFinset (matchingCyclicDiagonalEmbedding hk t j) =
      cyclicMatchingBlock hk t j := by
  classical
  ext i
  rw [mem_matchingMarkedFinset]
  constructor
  · rintro ⟨y, hy⟩
    change (matchingCyclicBlockIndexEquiv hk t j y).1 = i at hy
    rw [← hy]
    exact (matchingCyclicBlockIndexEquiv hk t j y).property
  · intro hi
    obtain ⟨y, hy⟩ :=
      (matchingCyclicBlockIndexEquiv hk t j).surjective ⟨i, hi⟩
    refine ⟨y, ?_⟩
    change (matchingCyclicBlockIndexEquiv hk t j y).1 = i
    exact congrArg Subtype.val hy
end PermanentFormulaLowerBound

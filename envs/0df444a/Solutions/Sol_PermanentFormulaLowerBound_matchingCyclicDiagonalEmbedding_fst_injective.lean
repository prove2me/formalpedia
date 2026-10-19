-- Prove2me | solution 1 for PermanentFormulaLowerBound.matchingCyclicDiagonalEmbedding_fst_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.787743+00:00
-- url     : https://prove2.me/submissions/55bad234-8bd6-49ed-ba13-dbc5393dcbe2

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_cyclicMatchingBlock_fst_injective

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
    Function.Injective
      (fun y => (matchingCyclicDiagonalEmbedding hk t j y).1) := by
  change Function.Injective
    (fun y => (matchingCyclicBlockIndexEquiv hk t j y).1.1)
  exact
    (cyclicMatchingBlock_fst_injective hk t j).comp
      (matchingCyclicBlockIndexEquiv hk t j).injective
end PermanentFormulaLowerBound

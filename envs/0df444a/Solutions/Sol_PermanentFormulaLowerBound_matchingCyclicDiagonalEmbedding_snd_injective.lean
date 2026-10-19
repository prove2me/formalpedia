-- Prove2me | solution 1 for PermanentFormulaLowerBound.matchingCyclicDiagonalEmbedding_snd_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.787743+00:00
-- url     : https://prove2.me/submissions/ab02591c-3629-4213-ae1e-9269d0e082b1

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_cyclicMatchingBlock_snd_injective

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
      (fun y => (matchingCyclicDiagonalEmbedding hk t j y).2) := by
  change Function.Injective
    (fun y => (matchingCyclicBlockIndexEquiv hk t j y).1.2)
  exact
    (cyclicMatchingBlock_snd_injective hk t j).comp
      (matchingCyclicBlockIndexEquiv hk t j).injective
end PermanentFormulaLowerBound

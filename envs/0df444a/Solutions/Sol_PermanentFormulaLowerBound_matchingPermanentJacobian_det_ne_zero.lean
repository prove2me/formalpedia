-- Prove2me | solution 1 for PermanentFormulaLowerBound.matchingPermanentJacobian_det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.787743+00:00
-- url     : https://prove2.me/submissions/479e3a19-fd5d-4ea7-b38d-1ca6f519eb16

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_matchingWeightedBivariateBitEvaluationMatrix_det_ne_zero
import Theorems.Thm_PermanentFormulaLowerBound_matchingPermanentJacobian_eq_weighted

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution
    {ell m : ℕ} (p q : Fin m → ℂ)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hm : m ≤ 2 ^ ell) (hroom : 2 * ell < m) :
    (matchingPermanentJacobian (ell := ell) p q).det ≠ 0 := by
  rw [matchingPermanentJacobian_eq_weighted]
  exact matchingWeightedBivariateBitEvaluationMatrix_det_ne_zero
    p q hp hq hm hroom
end PermanentFormulaLowerBound

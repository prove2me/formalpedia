-- Prove2me | solution 1 for PermanentFormulaLowerBound.matchingWeightedBivariateBitEvaluationMatrix_det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.22648+00:00
-- url     : https://prove2.me/submissions/78fd0b99-2d62-469b-9968-83d792e3aed3

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_matchingBinaryDegree_bitSubset
import Theorems.Thm_PermanentFormulaLowerBound_matchingWeightedBivariateEvaluationMatrix_det_ne_zero

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution
    {F : Type*} [Field F] [CharZero F] {ell m : ℕ}
    (p q : Fin m → F)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hm : m ≤ 2 ^ ell) (hroom : 2 * ell < m) :
    (matchingWeightedBivariateEvaluationMatrix p q
      (fun d : Fin m => matchingBitSubset ell (d : ℕ))
      (fun e : Fin m => matchingBitSubset ell (e : ℕ))).det ≠ 0 := by
  apply matchingWeightedBivariateEvaluationMatrix_det_ne_zero
    p q hp hq _ _ _ _ hroom
  · intro d
    exact matchingBinaryDegree_bitSubset ell d (lt_of_lt_of_le d.isLt hm)
  · intro e
    exact matchingBinaryDegree_bitSubset ell e (lt_of_lt_of_le e.isLt hm)
end PermanentFormulaLowerBound

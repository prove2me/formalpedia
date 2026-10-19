-- Prove2me | solution 1 for PermanentFormulaLowerBound.matchingBivariateEvaluationMatrix_det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.22648+00:00
-- url     : https://prove2.me/submissions/63f7dac8-c4a4-4514-b436-d4f4950376c3

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_matchingPolynomialEvaluationMatrix_det_ne_zero
import Theorems.Thm_PermanentFormulaLowerBound_matchingBivariateEvaluationMatrix_eq_kronecker

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
    (P Q : Fin m → Finset (Fin ell))
    (hP : ∀ d : Fin m, matchingBinaryDegree (P d) = (d : ℕ))
    (hQ : ∀ e : Fin m, matchingBinaryDegree (Q e) = (e : ℕ)) :
    (matchingBivariateEvaluationMatrix p q P Q).det ≠ 0 := by
  have hpdet := matchingPolynomialEvaluationMatrix_det_ne_zero p hp P hP
  have hqdet := matchingPolynomialEvaluationMatrix_det_ne_zero q hq Q hQ
  rw [matchingBivariateEvaluationMatrix_eq_kronecker,
    Matrix.det_permute', Matrix.det_kronecker]
  rcases Int.units_eq_one_or
    (Equiv.Perm.sign (Equiv.prodComm (Fin m) (Fin m))) with hsign | hsign
  · simp [hsign, hpdet, hqdet]
  · simp [hsign, hpdet, hqdet]
end PermanentFormulaLowerBound

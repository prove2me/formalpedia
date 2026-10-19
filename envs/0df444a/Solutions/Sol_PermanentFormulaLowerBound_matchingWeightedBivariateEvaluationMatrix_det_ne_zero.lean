-- Prove2me | solution 1 for PermanentFormulaLowerBound.matchingWeightedBivariateEvaluationMatrix_det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.22648+00:00
-- url     : https://prove2.me/submissions/c10af1c7-02d5-49b1-9910-1ca718622d38

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_matchingBivariateEvaluationMatrix_det_ne_zero
import Theorems.Thm_PermanentFormulaLowerBound_matchingJacobianWeight_pos
import Theorems.Thm_PermanentFormulaLowerBound_matchingWeightedBivariateEvaluationMatrix_eq_diagonal_mul

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
    (hQ : ∀ e : Fin m, matchingBinaryDegree (Q e) = (e : ℕ))
    (hroom : 2 * ell < m) :
    (matchingWeightedBivariateEvaluationMatrix p q P Q).det ≠ 0 := by
  classical
  rw [matchingWeightedBivariateEvaluationMatrix_eq_diagonal_mul,
    Matrix.det_mul, Matrix.det_diagonal]
  apply mul_ne_zero
  · apply Finset.prod_ne_zero_iff.mpr
    intro de _
    have hcardP : (P de.1).card ≤ ell := by
      simpa using Finset.card_le_univ (P de.1)
    have hcardQ : (Q de.2).card ≤ ell := by
      simpa using Finset.card_le_univ (Q de.2)
    have hfit : (P de.1).card + (Q de.2).card < m := by omega
    exact Nat.cast_ne_zero.mpr
      ((matchingJacobianWeight_pos m (P de.1).card (Q de.2).card hfit).ne')
  · exact matchingBivariateEvaluationMatrix_det_ne_zero
      p q hp hq P Q hP hQ
end PermanentFormulaLowerBound

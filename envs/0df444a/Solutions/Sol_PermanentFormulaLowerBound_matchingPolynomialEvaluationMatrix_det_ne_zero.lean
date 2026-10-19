-- Prove2me | solution 1 for PermanentFormulaLowerBound.matchingPolynomialEvaluationMatrix_det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.22648+00:00
-- url     : https://prove2.me/submissions/c9d30157-9103-4cd0-a9c6-ecea7fa32745

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_matchingPolynomial_coeff_binaryDegree_ne_zero
import Theorems.Thm_PermanentFormulaLowerBound_matchingPolynomial_natDegree

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution
    {F : Type*} [Field F] [CharZero F] {ell m : ℕ}
    (p : Fin m → F) (hp : Function.Injective p)
    (P : Fin m → Finset (Fin ell))
    (hP : ∀ d : Fin m, matchingBinaryDegree (P d) = (d : ℕ)) :
    (matchingPolynomialEvaluationMatrix p P).det ≠ 0 := by
  classical
  let g : Fin m → Polynomial F := fun d => matchingPolynomial p (P d)
  have hdegree (d : Fin m) : (g d).natDegree = (d : ℕ) := by
    exact (matchingPolynomial_natDegree p (P d)).trans (hP d)
  change (Matrix.of (fun b d : Fin m => (g d).eval (p b))).det ≠ 0
  rw [Matrix.eval_matrixOfPolynomials_eq_vandermonde_mul_matrixOfPolynomials
    p g (fun d => (hdegree d).le), Matrix.det_mul]
  apply mul_ne_zero
  · exact Matrix.det_vandermonde_ne_zero_iff.mpr hp
  · rw [Matrix.det_of_upperTriangular
      (Matrix.matrixOfPolynomials_blockTriangular g
        (fun d => (hdegree d).le))]
    apply Finset.prod_ne_zero_iff.mpr
    intro d _
    change (matchingPolynomial p (P d)).coeff (d : ℕ) ≠ 0
    rw [← hP d]
    exact matchingPolynomial_coeff_binaryDegree_ne_zero p (P d)
end PermanentFormulaLowerBound

-- Prove2me | solution 1 for PermanentRollout.homogeneousMapFinSuccFirstPivotPlaneMap_substitution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.983104+00:00
-- url     : https://prove2.me/submissions/df062ee0-89ca-4b90-b85c-9be90b4325be

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_homogeneousMapFinSuccFirstPivotPlaneMap_coordinate_zero
import Theorems.Thm_PermanentRollout_homogeneousMapFinSuccFirstPivotPlaneMap_coordinate_succ

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped nonZeroDivisors Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
open scoped BigOperators
open scoped Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution
    {n : ℕ} (c : Fin (n + 1) → ℂ)
    (p : MvPolynomial (Fin (n + 1)) ℂ) :
    (MvPolynomial.finSuccEquiv ℂ n p).eval
        (homogeneousMapFinSuccFirstPivotPlaneRoot c) =
      MvPolynomial.aeval
        (fun row => linearCoordinatePolynomial
          (homogeneousMapFinSuccFirstPivotPlaneMap c) row) p := by
  classical
  induction p using MvPolynomial.induction_on with
  | C z =>
      simpa using congrArg
        (Polynomial.eval (homogeneousMapFinSuccFirstPivotPlaneRoot c))
        ((MvPolynomial.finSuccEquiv ℂ n).commutes z)
  | add f g hf hg => simp [map_add, Polynomial.eval_add, hf, hg]
  | mul_X f i hf =>
      simp only [map_mul, Polynomial.eval_mul, MvPolynomial.aeval_X]
      rw [hf]
      cases i using Fin.cases with
      | zero =>
          simp [MvPolynomial.finSuccEquiv_X_zero,
            homogeneousMapFinSuccFirstPivotPlaneMap_coordinate_zero]
      | succ i =>
          rw [MvPolynomial.finSuccEquiv_X_succ,
            Polynomial.eval_C,
            homogeneousMapFinSuccFirstPivotPlaneMap_coordinate_succ]
end PermanentRollout

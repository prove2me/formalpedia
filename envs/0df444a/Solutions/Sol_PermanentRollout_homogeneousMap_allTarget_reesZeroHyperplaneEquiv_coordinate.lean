-- Prove2me | solution 1 for PermanentRollout.homogeneousMap_allTarget_reesZeroHyperplaneEquiv_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:04.538453+00:00
-- url     : https://prove2.me/submissions/db0c9a54-048d-4435-aa40-dd5b4d221b42

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_homogeneousMap_allTarget_reesZeroHyperplaneEquiv_mk
import Theorems.Thm_PermanentRollout_homogeneousMap_allTarget_finSucc_rename_eval_zero

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
open scoped Pointwise BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped Pointwise BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped Pointwise BigOperators
open scoped BigOperators
open scoped Pointwise
open scoped BigOperators
open scoped Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped Pointwise BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped Pointwise BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {k : ℕ} (F : Fin k → MvPolynomial (Fin k) ℂ)
    (target : Fin k → ℂ) (e : ℕ) (he : 0 < e)
    (i : Fin k) :
    homogeneousMapAllTargetReesZeroHyperplaneEquiv k
      (Ideal.Quotient.mk
        (Ideal.span ({MvPolynomial.X (0 : Fin (k + 1))} :
          Set (MvPolynomial (Fin (k + 1)) ℂ)))
        (homogeneousMapAllTargetReesCoordinate F target e i)) = F i := by
  rw [homogeneousMap_allTarget_reesZeroHyperplaneEquiv_mk]
  unfold homogeneousMapAllTargetReesCoordinate
  rw [map_sub, Polynomial.eval_sub, map_mul, Polynomial.eval_mul,
    map_pow, Polynomial.eval_pow,
    MvPolynomial.finSuccEquiv_X_zero, Polynomial.eval_X,
    zero_pow (Nat.ne_of_gt he), mul_zero, sub_zero]
  exact homogeneousMap_allTarget_finSucc_rename_eval_zero (F i)
end PermanentRollout

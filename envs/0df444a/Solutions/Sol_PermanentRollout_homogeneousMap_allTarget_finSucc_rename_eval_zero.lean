-- Prove2me | solution 1 for PermanentRollout.homogeneousMap_allTarget_finSucc_rename_eval_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:04.538453+00:00
-- url     : https://prove2.me/submissions/5e83b7d0-009b-45d8-9ecd-6cb67d628ac6

import Mathlib
import Definitions.Def_Permanent

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
    {k : ℕ} (p : MvPolynomial (Fin k) ℂ) :
    (MvPolynomial.finSuccEquiv ℂ k
      (MvPolynomial.rename Fin.succ p)).eval 0 = p := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      simpa using congrArg (Polynomial.eval
        (0 : MvPolynomial (Fin k) ℂ))
        ((MvPolynomial.finSuccEquiv ℂ k).commutes a)
  | add p q hp hq =>
      simp [map_add, Polynomial.eval_add, hp, hq]
  | mul_X p i hp =>
      simp [map_mul, Polynomial.eval_mul,
        MvPolynomial.finSuccEquiv_X_succ, hp]
end PermanentRollout

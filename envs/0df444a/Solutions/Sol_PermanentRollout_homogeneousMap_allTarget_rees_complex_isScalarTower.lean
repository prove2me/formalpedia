-- Prove2me | solution 1 for PermanentRollout.homogeneousMap_allTarget_rees_complex_isScalarTower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.100639+00:00
-- url     : https://prove2.me/submissions/895ed668-6cf6-48f5-a6a2-5e080f77ce1a

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
open scoped TensorProduct
namespace PermanentRollout
theorem _root_.solution
    {k : ℕ} (F : Fin k → MvPolynomial (Fin k) ℂ)
    (target : Fin k → ℂ) (e : ℕ) :
    letI : Algebra (Polynomial ℂ)
      (homogeneousMapAllTargetReesQuotient F target e) :=
        homogeneousMapAllTargetReesParameterAlgebra F target e
    IsScalarTower ℂ (Polynomial ℂ)
      (homogeneousMapAllTargetReesQuotient F target e) := by
  letI : Algebra (Polynomial ℂ)
      (homogeneousMapAllTargetReesQuotient F target e) :=
    homogeneousMapAllTargetReesParameterAlgebra F target e
  apply IsScalarTower.of_algebraMap_eq
  intro c
  change Ideal.Quotient.mk
      (Ideal.span (Set.range
        (homogeneousMapAllTargetReesCoordinate F target e)))
      (MvPolynomial.C c) =
    Ideal.Quotient.mk
      (Ideal.span (Set.range
        (homogeneousMapAllTargetReesCoordinate F target e)))
      ((Polynomial.aeval
        (MvPolynomial.X (R := ℂ) (0 : Fin (k + 1))))
        (Polynomial.C c))
  simp
end PermanentRollout

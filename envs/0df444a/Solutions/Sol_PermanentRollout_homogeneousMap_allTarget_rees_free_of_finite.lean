-- Prove2me | solution 1 for PermanentRollout.homogeneousMap_allTarget_rees_free_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.100639+00:00
-- url     : https://prove2.me/submissions/53e3bee5-e303-40be-9941-e21f477da3bc

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_homogeneousMap_allTarget_reesParameter_isTorsionFree

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
    (target : Fin k → ℂ) (e : ℕ) (he : 0 < e)
    (hF : ∀ i, (F i).IsHomogeneous e)
    (hzero : ∀ point : Fin k → ℂ,
      (∀ i, MvPolynomial.eval point (F i) = 0) ↔ point = 0)
    (hfinite :
      letI : Algebra (Polynomial ℂ)
        (homogeneousMapAllTargetReesQuotient F target e) :=
          homogeneousMapAllTargetReesParameterAlgebra F target e
      Module.Finite (Polynomial ℂ)
        (homogeneousMapAllTargetReesQuotient F target e)) :
    letI : Algebra (Polynomial ℂ)
      (homogeneousMapAllTargetReesQuotient F target e) :=
        homogeneousMapAllTargetReesParameterAlgebra F target e
    Module.Free (Polynomial ℂ)
      (homogeneousMapAllTargetReesQuotient F target e) := by
  letI : Algebra (Polynomial ℂ)
      (homogeneousMapAllTargetReesQuotient F target e) :=
    homogeneousMapAllTargetReesParameterAlgebra F target e
  letI : Module.Finite (Polynomial ℂ)
      (homogeneousMapAllTargetReesQuotient F target e) := hfinite
  letI : Module.IsTorsionFree (Polynomial ℂ)
      (homogeneousMapAllTargetReesQuotient F target e) :=
    homogeneousMap_allTarget_reesParameter_isTorsionFree
      F target e he hF hzero
  exact Module.free_of_finite_type_torsion_free'
end PermanentRollout

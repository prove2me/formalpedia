-- Prove2me | solution 1 for PermanentRollout.homogeneousMap_allTarget_rees_parameterFiber_finrank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.100639+00:00
-- url     : https://prove2.me/submissions/2ae7cbeb-aef0-4f26-a169-5c098f36bd98

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_finiteFree_complexTargetFiber_finrank
import Theorems.Thm_PermanentRollout_homogeneousMap_allTarget_rees_complex_isScalarTower
import Theorems.Thm_PermanentRollout_homogeneousMap_allTarget_rees_free_of_finite

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
        (homogeneousMapAllTargetReesQuotient F target e))
    (a : ℂ) :
    letI : Algebra (Polynomial ℂ)
      (homogeneousMapAllTargetReesQuotient F target e) :=
        homogeneousMapAllTargetReesParameterAlgebra F target e
    Module.finrank ℂ
      (homogeneousMapAllTargetReesQuotient F target e ⧸
        (RingHom.ker (Polynomial.aeval a).toRingHom).map
          (algebraMap (Polynomial ℂ)
            (homogeneousMapAllTargetReesQuotient F target e))) =
      Module.finrank (Polynomial ℂ)
        (homogeneousMapAllTargetReesQuotient F target e) := by
  letI : Algebra (Polynomial ℂ)
      (homogeneousMapAllTargetReesQuotient F target e) :=
    homogeneousMapAllTargetReesParameterAlgebra F target e
  letI : IsScalarTower ℂ (Polynomial ℂ)
      (homogeneousMapAllTargetReesQuotient F target e) :=
    homogeneousMap_allTarget_rees_complex_isScalarTower F target e
  letI : Module.Free (Polynomial ℂ)
      (homogeneousMapAllTargetReesQuotient F target e) :=
    homogeneousMap_allTarget_rees_free_of_finite
      F target e he hF hzero hfinite
  apply finiteFree_complexTargetFiber_finrank (Polynomial.aeval a)
  intro c
  exact ⟨Polynomial.C c, by simp⟩
end PermanentRollout

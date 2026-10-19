-- Prove2me | solution 1 for PermanentRollout.homogeneousMap_closedFiber_finrank_of_rees_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.100639+00:00
-- url     : https://prove2.me/submissions/bfa2268b-ace5-4e66-a67d-2742f3466383

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_homogeneousMap_zeroClosedFiber_finrank
import Theorems.Thm_PermanentRollout_homogeneousMap_allTarget_rees_parameterFiber_finrank

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
    (k : ℕ) (F : Fin k → MvPolynomial (Fin k) ℂ)
    (e : ℕ) (he : 0 < e)
    (hF : ∀ i, (F i).IsHomogeneous e)
    (hzero : ∀ point : Fin k → ℂ,
      (∀ i, MvPolynomial.eval point (F i) = 0) ↔ point = 0)
    (target : Fin k → ℂ)
    (hfinite :
      letI : Algebra (Polynomial ℂ)
        (homogeneousMapAllTargetReesQuotient F target e) :=
          homogeneousMapAllTargetReesParameterAlgebra F target e
      Module.Finite (Polynomial ℂ)
        (homogeneousMapAllTargetReesQuotient F target e)) :
    Module.finrank ℂ (homogeneousMapClosedFiber F target) = e ^ k := by
  let A := homogeneousMapAllTargetReesQuotient F target e
  letI : Algebra (Polynomial ℂ) A :=
    homogeneousMapAllTargetReesParameterAlgebra F target e
  have hparameter (a : ℂ) :
      Module.finrank ℂ
        (A ⧸ (RingHom.ker (Polynomial.evalRingHom a)).map
          (algebraMap (Polynomial ℂ) A)) =
        Module.finrank (Polynomial ℂ) A := by
    exact homogeneousMap_allTarget_rees_parameterFiber_finrank
      F target e he hF hzero hfinite a
  have htarget :=
    (homogeneousMapAllTargetReesPolynomialParameterFiberEquiv
      F target e 1).toLinearEquiv.finrank_eq
  have hzeroFiber :=
    (homogeneousMapAllTargetReesPolynomialParameterFiberEquiv
      F target e 0).toLinearEquiv.finrank_eq
  have htarget_scale :
      (fun i : Fin k => target i * (1 : ℂ) ^ e) = target := by
    funext i
    simp
  have hzero_scale :
      (fun i : Fin k => target i * (0 : ℂ) ^ e) =
        (0 : Fin k → ℂ) := by
    funext i
    simp [zero_pow he.ne']
  rw [htarget_scale] at htarget
  rw [hzero_scale] at hzeroFiber
  calc
    Module.finrank ℂ (homogeneousMapClosedFiber F target) =
        Module.finrank ℂ
          (A ⧸ (RingHom.ker (Polynomial.evalRingHom 1)).map
            (algebraMap (Polynomial ℂ) A)) := htarget.symm
    _ = Module.finrank (Polynomial ℂ) A := hparameter 1
    _ = Module.finrank ℂ
          (A ⧸ (RingHom.ker (Polynomial.evalRingHom 0)).map
            (algebraMap (Polynomial ℂ) A)) := (hparameter 0).symm
    _ = Module.finrank ℂ (homogeneousMapClosedFiber F 0) := hzeroFiber
    _ = e ^ k := homogeneousMap_zeroClosedFiber_finrank k F e he hF hzero
end PermanentRollout

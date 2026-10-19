-- Prove2me | solution 1 for PermanentRollout.homogeneousMap_allTarget_rees_polynomial_parameter_isSMulRegular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:04.538453+00:00
-- url     : https://prove2.me/submissions/dbe9d2c7-b6db-4d04-ad68-240a63eb6407

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_homogeneousMap_allTarget_homogeneous_aeval_isSMulRegular
import Theorems.Thm_PermanentRollout_homogeneousMap_allTarget_reesCoordinate_isHomogeneous
import Theorems.Thm_PermanentRollout_homogeneousMap_allTarget_rees_parameter_isSMulRegular

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
    (hF : ∀ i, (F i).IsHomogeneous e)
    (hzero : ∀ point : Fin k → ℂ,
      (∀ i, MvPolynomial.eval point (F i) = 0) ↔ point = 0)
    (p : Polynomial ℂ) (hp : p ≠ 0) :
    IsSMulRegular
      (MvPolynomial (Fin (k + 1)) ℂ ⧸
        Ideal.span (Set.range (homogeneousMapAllTargetReesCoordinate F target e)))
      (Polynomial.aeval
        (MvPolynomial.X (R := ℂ) (0 : Fin (k + 1))) p) := by
  apply homogeneousMap_allTarget_homogeneous_aeval_isSMulRegular
    (Ideal.span (Set.range (homogeneousMapAllTargetReesCoordinate F target e)))
  · apply Ideal.homogeneous_span
    rintro _ ⟨i, rfl⟩
    exact ⟨e, homogeneousMap_allTarget_reesCoordinate_isHomogeneous
      F target e hF i⟩
  · exact MvPolynomial.isHomogeneous_X ℂ 0
  · exact homogeneousMap_allTarget_rees_parameter_isSMulRegular
      F target e he hF hzero
  · exact hp
end PermanentRollout

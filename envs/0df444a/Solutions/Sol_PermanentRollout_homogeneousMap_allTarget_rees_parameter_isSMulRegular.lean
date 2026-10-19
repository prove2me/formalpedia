-- Prove2me | solution 1 for PermanentRollout.homogeneousMap_allTarget_rees_parameter_isSMulRegular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:04.538453+00:00
-- url     : https://prove2.me/submissions/2de0bd4a-6eee-4232-8001-1bb879990225

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_homogeneousMap_allRank_fin_hyperplane_isSMulRegular_of_quotient_weaklyRegular
import Theorems.Thm_PermanentRollout_homogeneousMap_allTarget_reesCoordinate_quotient_isWeaklyRegular

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
      (∀ i, MvPolynomial.eval point (F i) = 0) ↔ point = 0) :
    IsSMulRegular
      (MvPolynomial (Fin (k + 1)) ℂ ⧸
        Ideal.span (Set.range (homogeneousMapAllTargetReesCoordinate F target e)))
      (MvPolynomial.X (R := ℂ) (0 : Fin (k + 1))) := by
  apply homogeneousMap_allRank_fin_hyperplane_isSMulRegular_of_quotient_weaklyRegular
    (homogeneousMapAllTargetReesCoordinate F target e)
    (MvPolynomial.X (R := ℂ) (0 : Fin (k + 1)))
    (MvPolynomial.X_ne_zero (R := ℂ) (0 : Fin (k + 1)))
  exact homogeneousMap_allTarget_reesCoordinate_quotient_isWeaklyRegular
    F target e he hF hzero
end PermanentRollout

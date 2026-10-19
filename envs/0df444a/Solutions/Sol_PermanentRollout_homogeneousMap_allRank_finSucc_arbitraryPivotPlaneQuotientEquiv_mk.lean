-- Prove2me | solution 1 for PermanentRollout.homogeneousMap_allRank_finSucc_arbitraryPivotPlaneQuotientEquiv_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.983104+00:00
-- url     : https://prove2.me/submissions/ac9a3dd1-3433-4438-bdb5-9ab74c3ca913

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
namespace PermanentRollout
theorem _root_.solution
    {n : ℕ} (c : Fin (n + 1) → ℂ)
    (j : Fin (n + 1)) (hj : c j ≠ 0)
    (p : MvPolynomial (Fin (n + 1)) ℂ) :
    homogeneousMapFinSuccArbitraryPivotPlaneQuotientEquiv c j hj
      (Ideal.Quotient.mk
        (Ideal.span
          ({permanentRolloutLinearCoordinateCombination (n + 1) c} :
            Set (MvPolynomial (Fin (n + 1)) ℂ))) p) =
      (MvPolynomial.finSuccEquiv ℂ n
        (MvPolynomial.rename (Equiv.swap (0 : Fin (n + 1)) j) p)).eval
          (homogeneousMapFinSuccLinearPlaneRoot
            (fun i => c ((Equiv.swap (0 : Fin (n + 1)) j).symm i))) := by
  rfl
end PermanentRollout

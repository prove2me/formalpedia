-- Prove2me | solution 1 for PermanentRollout.homogeneousMap_allRank_finSucc_arbitraryPivotPlaneQuotientEquiv_mk_eq_aeval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:04.538453+00:00
-- url     : https://prove2.me/submissions/85cc595c-3f4a-4c53-b3c8-384052aabef4

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_homogeneousMap_allRank_finSucc_arbitraryPivotPlaneQuotientEquiv_mk
import Theorems.Thm_PermanentRollout_homogeneousMapFinSuccArbitraryPivotPlaneMap_substitution

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
    (j : Fin (n + 1)) (hj : c j ≠ 0)
    (p : MvPolynomial (Fin (n + 1)) ℂ) :
    homogeneousMapFinSuccArbitraryPivotPlaneQuotientEquiv c j hj
      (Ideal.Quotient.mk
        (Ideal.span
          ({permanentRolloutLinearCoordinateCombination (n + 1) c} :
            Set (MvPolynomial (Fin (n + 1)) ℂ))) p) =
      MvPolynomial.aeval
        (fun row => linearCoordinatePolynomial
          (homogeneousMapFinSuccArbitraryPivotPlaneMap c j) row) p := by
  rw [homogeneousMap_allRank_finSucc_arbitraryPivotPlaneQuotientEquiv_mk]
  change
    (MvPolynomial.finSuccEquiv ℂ n
      (MvPolynomial.rename (Equiv.swap (0 : Fin (n + 1)) j) p)).eval
        (homogeneousMapFinSuccFirstPivotPlaneRoot
          (fun i => c ((Equiv.swap (0 : Fin (n + 1)) j).symm i))) = _
  exact homogeneousMapFinSuccArbitraryPivotPlaneMap_substitution c j p
end PermanentRollout

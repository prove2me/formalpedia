-- Prove2me | solution 1 for PermanentRollout.homogeneousMapFinSuccFirstPivotPlaneMap_coordinate_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.983104+00:00
-- url     : https://prove2.me/submissions/2eeb4312-dd33-4da8-b137-830cfc793703

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_linearCoordinatePolynomial_eval

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
    {n : ℕ} (c : Fin (n + 1) → ℂ) :
    linearCoordinatePolynomial
      (homogeneousMapFinSuccFirstPivotPlaneMap c) 0 =
      homogeneousMapFinSuccFirstPivotPlaneRoot c := by
  classical
  apply MvPolynomial.funext
  intro u
  rw [linearCoordinatePolynomial_eval]
  simp [homogeneousMapFinSuccFirstPivotPlaneMap,
    homogeneousMapFinSuccFirstPivotPlaneRoot]
end PermanentRollout

-- Prove2me | solution 1 for PermanentRollout.homogeneousMapFinSuccFirstPivotPlaneMap_coordinate_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.983104+00:00
-- url     : https://prove2.me/submissions/7b016d3c-bcf4-40f1-bdd0-ef63c0e1f191

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
    {n : ℕ} (c : Fin (n + 1) → ℂ) (i : Fin n) :
    linearCoordinatePolynomial
      (homogeneousMapFinSuccFirstPivotPlaneMap c) i.succ =
      MvPolynomial.X i := by
  classical
  apply MvPolynomial.funext
  intro u
  rw [linearCoordinatePolynomial_eval]
  simp [homogeneousMapFinSuccFirstPivotPlaneMap]
end PermanentRollout

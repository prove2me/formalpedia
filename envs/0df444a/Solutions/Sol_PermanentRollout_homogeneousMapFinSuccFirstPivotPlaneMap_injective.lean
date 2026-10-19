-- Prove2me | solution 1 for PermanentRollout.homogeneousMapFinSuccFirstPivotPlaneMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.983104+00:00
-- url     : https://prove2.me/submissions/e5718359-8f06-45d3-bbc4-d80d97ac2106

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
namespace PermanentRollout
theorem _root_.solution
    {n : ℕ} (c : Fin (n + 1) → ℂ) :
    Function.Injective (homogeneousMapFinSuccFirstPivotPlaneMap c) := by
  intro u v huv
  funext i
  simpa only [homogeneousMapFinSuccFirstPivotPlaneMap,
    LinearMap.pi_apply, Fin.cases_succ, LinearMap.proj_apply] using
    congrFun huv i.succ
end PermanentRollout

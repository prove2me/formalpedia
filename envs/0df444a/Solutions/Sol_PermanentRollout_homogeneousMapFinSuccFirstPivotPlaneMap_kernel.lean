-- Prove2me | solution 1 for PermanentRollout.homogeneousMapFinSuccFirstPivotPlaneMap_kernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.983104+00:00
-- url     : https://prove2.me/submissions/0af5a7c7-d152-4085-a451-8cf0ef1658b2

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
    {n : ℕ} (c : Fin (n + 1) → ℂ)
    (hc : c 0 ≠ 0) (u : Fin n → ℂ) :
    ∑ i : Fin (n + 1),
      c i * homogeneousMapFinSuccFirstPivotPlaneMap c u i = 0 := by
  rw [Fin.sum_univ_succ]
  simp [homogeneousMapFinSuccFirstPivotPlaneMap]
  field_simp
  ring
end PermanentRollout

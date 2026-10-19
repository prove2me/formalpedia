-- Prove2me | solution 1 for PermanentRollout.homogeneousMap_allRank_coordinateSubsetIdeal_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:04.538453+00:00
-- url     : https://prove2.me/submissions/45e2f708-5b9b-4c2b-a4c8-cbf5080a4a00

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
namespace PermanentRollout
theorem _root_.solution
    {k : ℕ} (F : Fin k → MvPolynomial (Fin k) ℂ)
    (restricted : Finset (Fin k)) (j : Fin k) :
    homogeneousMapAllKCoordinateSubsetIdeal F (insert j restricted) =
      homogeneousMapAllKCoordinateSubsetIdeal F restricted ⊔
        Ideal.span ({F j} : Set (MvPolynomial (Fin k) ℂ)) := by
  unfold homogeneousMapAllKCoordinateSubsetIdeal
  rw [← Ideal.span_union]
  congr 1
  ext p
  simp [eq_comm]
end PermanentRollout

-- Prove2me | solution 1 for PermanentRollout.homogeneousMap_allRank_coordinateSubsetIdeal_isHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:04.538453+00:00
-- url     : https://prove2.me/submissions/499127eb-e73c-4b0a-b090-2537d23f4467

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
    {k e : ℕ} (F : Fin k → MvPolynomial (Fin k) ℂ)
    (hF : ∀ i, (F i).IsHomogeneous e)
    (restricted : Finset (Fin k)) :
    (homogeneousMapAllKCoordinateSubsetIdeal F restricted).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin k) ℂ) := by
  apply Ideal.homogeneous_span
  rintro _ ⟨i, _, rfl⟩
  exact ⟨e, hF i⟩
end PermanentRollout

-- Prove2me | solution 1 for PermanentRollout.homogeneousMap_allRank_bounded_homogeneous_hilbert_coefficient_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:04.538453+00:00
-- url     : https://prove2.me/submissions/6f87bba4-d654-46ea-ab1c-87972b3a10d4

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
namespace PermanentRollout
theorem _root_.solution
    (k e n : ℕ) :
    homogeneousMapAllKBoundedHomogeneousHilbertCoefficient k e n ∅ =
      (k + n - 1).choose n := by
  classical
  simpa [homogeneousMapAllKBoundedHomogeneousHilbertCoefficient] using
    (Finset.card_finsuppAntidiag_nat_eq_choose
      (s := (Finset.univ : Finset (Fin k))) n)
end PermanentRollout

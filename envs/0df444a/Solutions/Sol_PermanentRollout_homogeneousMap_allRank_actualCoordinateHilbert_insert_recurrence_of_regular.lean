-- Prove2me | solution 1 for PermanentRollout.homogeneousMap_allRank_actualCoordinateHilbert_insert_recurrence_of_regular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:04.538453+00:00
-- url     : https://prove2.me/submissions/9477d95f-6710-43dc-b2fa-ffab17e4eb13

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_homogeneousMapGradedSupSpan_finrank_add_of_regular
import Theorems.Thm_PermanentRollout_homogeneousMap_allRank_coordinateSubsetIdeal_isHomogeneous
import Theorems.Thm_PermanentRollout_homogeneousMap_allRank_coordinateSubsetIdeal_insert

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
    (restricted : Finset (Fin k)) (j : Fin k)
    (hregular : IsSMulRegular
      (MvPolynomial (Fin k) ℂ ⧸ homogeneousMapAllKCoordinateSubsetIdeal F restricted)
      (F j))
    (n : ℕ) :
    homogeneousMapAllKActualCoordinateHilbert F (insert j restricted) (e + n) +
      homogeneousMapAllKActualCoordinateHilbert F restricted n =
      homogeneousMapAllKActualCoordinateHilbert F restricted (e + n) := by
  have hrec := homogeneousMapGradedSupSpan_finrank_add_of_regular
    (homogeneousMapAllKCoordinateSubsetIdeal F restricted)
    (homogeneousMap_allRank_coordinateSubsetIdeal_isHomogeneous F hF restricted)
    (F j) (hF j) hregular n
  rw [← homogeneousMap_allRank_coordinateSubsetIdeal_insert] at hrec
  exact hrec
end PermanentRollout

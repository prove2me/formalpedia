-- Prove2me | solution 1 for PermanentRollout.homogeneousMap_allRank_actualCoordinateHilbert_insert_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:04.538453+00:00
-- url     : https://prove2.me/submissions/cb5bf9a0-d372-4cb6-97ca-8235d1f77090

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_homogeneousMap_allRank_coordinateSubsetGradedIdealPiece_eq_bot_of_lt

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
    (n : ℕ) (hn : n < e) :
    homogeneousMapAllKActualCoordinateHilbert F (insert j restricted) n =
      homogeneousMapAllKActualCoordinateHilbert F restricted n := by
  classical
  letI : Module.Finite ℂ
      (MvPolynomial.homogeneousSubmodule (Fin k) ℂ n) :=
    (Submodule.fg_iff_finiteDimensional _).mp
      (MvPolynomial.homogeneousSubmodule_fg (Fin k) ℂ n)
  have hleft := homogeneousMap_allRank_coordinateSubsetGradedIdealPiece_eq_bot_of_lt
    F hF (insert j restricted) n hn
  have hright := homogeneousMap_allRank_coordinateSubsetGradedIdealPiece_eq_bot_of_lt
    F hF restricted n hn
  unfold homogeneousMapAllKActualCoordinateHilbert
  exact (Submodule.quotEquivOfEq _ _
    (hleft.trans hright.symm)).finrank_eq
end PermanentRollout

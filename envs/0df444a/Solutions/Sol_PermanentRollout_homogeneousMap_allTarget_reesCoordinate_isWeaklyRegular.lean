-- Prove2me | solution 1 for PermanentRollout.homogeneousMap_allTarget_reesCoordinate_isWeaklyRegular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.813979+00:00
-- url     : https://prove2.me/submissions/9c74bc04-b936-4312-b7e5-57b6217823fc

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_homogeneousMap_allRank_homogeneous_fin_isWeaklyRegular_of_linear_quotient_aux
import Theorems.Thm_PermanentRollout_homogeneousMap_allTarget_reesCoordinate_isHomogeneous
import Theorems.Thm_PermanentRollout_homogeneousMap_allTarget_reesCoordinate_quotient_isWeaklyRegular

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators Topology Pointwise
open Filter Asymptotics
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {k : ℕ} (F : Fin k → MvPolynomial (Fin k) ℂ)
    (target : Fin k → ℂ) (e : ℕ) (he : 0 < e)
    (hF : ∀ i, (F i).IsHomogeneous e)
    (hzero : ∀ point : Fin k → ℂ,
      (∀ i, MvPolynomial.eval point (F i) = 0) ↔ point = 0) :
    RingTheory.Sequence.IsWeaklyRegular
      (MvPolynomial (Fin (k + 1)) ℂ)
      (List.ofFn (homogeneousMapAllTargetReesCoordinate F target e)) := by
  apply homogeneousMap_allRank_homogeneous_fin_isWeaklyRegular_of_linear_quotient_aux
    (MvPolynomial.X (R := ℂ) (0 : Fin (k + 1)))
    (MvPolynomial.X_ne_zero (R := ℂ) (0 : Fin (k + 1)))
    (MvPolynomial.isHomogeneous_X ℂ 0)
    k (homogeneousMapAllTargetReesCoordinate F target e)
  · exact homogeneousMap_allTarget_reesCoordinate_isHomogeneous F target e hF
  · exact homogeneousMap_allTarget_reesCoordinate_quotient_isWeaklyRegular
      F target e he hF hzero
end PermanentRollout

-- Prove2me | solution 1 for PermanentRollout.homogeneousMap_allTarget_translated_isWeaklyRegular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.813979+00:00
-- url     : https://prove2.me/submissions/16c67503-d080-465a-9b99-1adf62574fe9

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_homogeneousMap_allRank_ringEquiv_isWeaklyRegular_iff_aux
import Theorems.Thm_PermanentRollout_homogeneousMap_allTarget_rees_chartCoordinate_isWeaklyRegular

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
      (MvPolynomial (Fin k) ℂ)
      (List.ofFn fun i : Fin k => F i - MvPolynomial.C (target i)) := by
  let E := homogeneousMapAllTargetReesChartHyperplaneEquiv k (1 : ℂ)
  have hchart := homogeneousMap_allTarget_rees_chartCoordinate_isWeaklyRegular
    F target e he hF hzero
  have himage :=
    (homogeneousMap_allRank_ringEquiv_isWeaklyRegular_iff_aux
      E.toRingEquiv
      (List.ofFn fun i : Fin k =>
        Ideal.Quotient.mk
          (homogeneousMapAllTargetReesChartIdeal k (1 : ℂ))
          (homogeneousMapAllTargetReesCoordinate F target e i))).mp hchart
  have hcoordinate (i : Fin k) :
      E.toRingEquiv (Ideal.Quotient.mk
        (homogeneousMapAllTargetReesChartIdeal k (1 : ℂ))
        (homogeneousMapAllTargetReesCoordinate F target e i)) =
          F i - MvPolynomial.C (target i) := by
    simpa [E] using
      homogeneousMap_allTarget_reesChartHyperplaneEquiv_coordinate
        F target e (1 : ℂ) i
  simpa only [List.map_ofFn, Function.comp_def, hcoordinate] using himage
end PermanentRollout

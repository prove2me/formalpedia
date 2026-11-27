-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_latticePointCount_hypotheses_unit_1d33f7a6c33d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:03:13.349353+00:00
-- url     : https://prove2.me/submissions/b2a776f0-c8c2-4a14-9c07-3c475760f58e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Points
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Slopes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
open MvPolynomial
open scoped ContDiff
open ReciprocityTheory.ChartRestriction.G.Geo (chartRingZ mCoordIdeal chartLat chartLatNm secM mcPts IsArithVar)
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
open AddBlockData
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
theorem _root_.solution :
    (0 : ℝ) < 1 ∧ LinearIndependent ℝ (EuclideanSpace.basisFun (Fin 1) ℝ) ∧
      (∀ s ∈ ({EuclideanSpace.basisFun (Fin 1) ℝ 0} : Finset (EuclideanSpace ℝ (Fin 1))), ‖s‖ ≤ 1) ∧
      AddSubgroup.closure
          (({EuclideanSpace.basisFun (Fin 1) ℝ 0} : Finset (EuclideanSpace ℝ (Fin 1))) :
            Set (EuclideanSpace ℝ (Fin 1))) =
        AddSubgroup.closure (Set.range (EuclideanSpace.basisFun (Fin 1) ℝ)) := by
  refine ⟨one_pos, (EuclideanSpace.basisFun (Fin 1) ℝ).orthonormal.linearIndependent, ?_, ?_⟩
  · intro s hs
    rw [Finset.mem_singleton] at hs
    subst hs
    exact ((EuclideanSpace.basisFun (Fin 1) ℝ).orthonormal.1 0).le
  · rw [Finset.coe_singleton, Set.range_unique]
    rfl
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

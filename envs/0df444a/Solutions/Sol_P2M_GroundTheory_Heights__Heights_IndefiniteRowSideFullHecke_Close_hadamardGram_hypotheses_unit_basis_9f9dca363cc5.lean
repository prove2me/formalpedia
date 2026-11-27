-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_hadamardGram_hypotheses_unit_basis_9f9dca363cc5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:57:05.86827+00:00
-- url     : https://prove2.me/submissions/f051b51c-5714-48ce-83d2-ec6e52671882

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
    LinearIndependent ℝ (EuclideanSpace.basisFun (Fin 1) ℝ) ∧
      (∀ i, ‖EuclideanSpace.basisFun (Fin 1) ℝ i‖ ≤ 1) ∧
      ∀ i, EuclideanSpace.basisFun (Fin 1) ℝ i ∈
        AddSubgroup.closure (Set.range (EuclideanSpace.basisFun (Fin 1) ℝ)) :=
  ⟨(EuclideanSpace.basisFun (Fin 1) ℝ).orthonormal.linearIndependent,
    fun i ↦ ((EuclideanSpace.basisFun (Fin 1) ℝ).orthonormal.1 i).le,
    fun i ↦ AddSubgroup.subset_closure (Set.mem_range_self i)⟩
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

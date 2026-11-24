-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_PointVertical_isMultiProjPrime_red_334bae5bc886
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:22:03.571797+00:00
-- url     : https://prove2.me/submissions/d3f207f0-cee6-44e4-aac7-b546f5eeb47f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsMultiHomogIdealChain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsMultiHomogFirstCoordinate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_TableDegreeThreeBase
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_ContractRelevant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContractedDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContracted
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsMultiProjPrimeImageZ
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PointVertical_red_surjective_25202236fa05
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PointVertical_ker_red_le_41d82c599a0f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PointVertical_mem_map_red_iff_50299f2085c4

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.Inter.PointVertical
variable {K : Type} {ι : K → Type} (p : ℕ)
namespace GroundTheory.Heights₂.Heights.Inter.PointVertical
theorem _root_.solution [∀ k, Fintype (ι k)] {J : Ideal (MRing ι)} (hJ : IsMultiProjPrime J)
    (hp : ((p : ℕ) : MRing ι) ∈ J) : IsMultiProjPrime (J.map (red p)) := by
  obtain ⟨hJp, ⟨S, hS, hJS⟩, hJr⟩ := hJ
  refine ⟨Ideal.map_isPrime_of_surjective (red_surjective p) (ker_red_le p hp),
    ⟨red p '' S, ?_, by rw [hJS, Ideal.map_span]⟩, fun k => ?_⟩
  · rintro _ ⟨f, hf, rfl⟩
    obtain ⟨a, ha⟩ := hS f hf
    exact ⟨a, fun m hm => ha m (support_map_subset _ _ hm)⟩
  · obtain ⟨i, hi⟩ := hJr k
    refine ⟨i, fun h => hi ((mem_map_red_iff p hp _).mp ?_)⟩
    rw [map_X]
    exact h
end GroundTheory.Heights₂.Heights.Inter.PointVertical

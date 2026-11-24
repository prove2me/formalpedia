-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_LocRingPow_component_mem_5ccd5932e898
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:31.72307+00:00
-- url     : https://prove2.me/submissions/560c9533-a7b6-473c-89d9-9812e70a3e59

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StLocRingPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PLocRingPow
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_LocRingPow_weight_multiDegWeight_ca852a704747
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_exists_blockComponent
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_isHomogeneous_of_isMultiHomogIdeal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.Inter.AvoidRing
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.LocRingPow
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter.LocRingPow
theorem _root_.solution [DecidableEq K] {J : Ideal (MRing ι)} (hJ : IsMultiHomogIdeal J) {f : MRing ι}
    (hf : f ∈ J) (D : K → ℕ) : weightedHomogeneousComponent (multiDegWeight ι) D f ∈ J := by
  obtain ⟨g, hg, hgc⟩ := exists_blockComponent (isHomogeneous_of_isMultiHomogIdeal hJ) D Finset.univ hf
  convert hg using 1
  ext m
  rw [coeff_weightedHomogeneousComponent, hgc, weight_multiDegWeight]
  by_cases h : ∀ k, ∑ i, m ⟨k, i⟩ = D k
  · simp [h]
  · simp [h, funext_iff]
end GroundTheory.Heights₂.Heights.Inter.LocRingPow

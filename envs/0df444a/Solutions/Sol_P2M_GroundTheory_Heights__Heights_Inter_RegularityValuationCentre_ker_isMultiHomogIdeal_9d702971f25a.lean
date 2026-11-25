-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_RegularityValuationCentre_ker_isMultiHomogIdeal_9d702971f25a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:24:42.628004+00:00
-- url     : https://prove2.me/submissions/12b1ab4e-3c00-4896-9a4a-739e73c5c76f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExistsIntValuationLtOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_KerIsMultiHomogIdeal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RegularityValuationCentre_specMap_component_5a8b2558d033
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_isMultiHomogIdeal_of_isHomogeneous


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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
attribute [local instance] MvPolynomial.weightedGradedAlgebra
open GroundTheory.Heights₂.Heights.Inter.RegularityValuationCentre
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
set_option backward.isDefEq.respectTransparency.types false
namespace GroundTheory.Heights₂.Heights.Inter.RegularityValuationCentre
theorem _root_.solution [DecidableEq K] {E : Type*} [Field E] (ψ : MRing ι →+* E) :
    IsMultiHomogIdeal (RingHom.ker (RegularityFunctionFieldNumber.specMap ψ ∅)) := by
  refine isMultiHomogIdeal_of_isHomogeneous fun k d g hg => ?_
  have hc : weightedHomogeneousComponent (blockWeight k) d g ∈ RingHom.ker (RegularityFunctionFieldNumber.specMap ψ ∅) := by
    rw [RingHom.mem_ker] at hg ⊢
    rw [specMap_component, hg, map_zero]
  rw [← weightedDecomposition.decompose'_apply] at hc
  exact hc
end GroundTheory.Heights₂.Heights.Inter.RegularityValuationCentre

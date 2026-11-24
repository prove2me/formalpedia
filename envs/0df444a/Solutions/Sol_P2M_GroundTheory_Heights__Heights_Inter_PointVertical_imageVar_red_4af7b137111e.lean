-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_PointVertical_imageVar_red_4af7b137111e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:22:03.256701+00:00
-- url     : https://prove2.me/submissions/514dd01a-ab7f-4286-bb78-a44bdf57ea01

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
variable {K' : Type} {ι' : K' → Type}
namespace GroundTheory.Heights₂.Heights.Inter.PointVertical
theorem _root_.solution [Fact p.Prime] (v : (Σ k, ι k) → (Σ k', ι' k')) {W : Ideal (MRing ι')}
    (hp : ((p : ℕ) : MRing ι') ∈ W) :
    imageVar (ZMod p) v (W.map (red p)) = (imageZ v W).map (red p) := by
  have hp' : ((p : ℕ) : MRing ι) ∈ imageZ v W := by
    show rename v ((p : ℕ) : MRing ι) ∈ W
    simpa using hp
  ext f
  obtain ⟨g, rfl⟩ := red_surjective p f
  rw [mem_map_red_iff p hp' g]
  show rename v (red p g) ∈ W.map (red p) ↔ rename v g ∈ W
  rw [← map_rename, mem_map_red_iff p hp]
end GroundTheory.Heights₂.Heights.Inter.PointVertical

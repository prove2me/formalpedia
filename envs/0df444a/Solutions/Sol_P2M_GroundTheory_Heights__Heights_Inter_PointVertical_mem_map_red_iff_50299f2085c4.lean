-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_PointVertical_mem_map_red_iff_50299f2085c4
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:29.92071+00:00
-- url     : https://prove2.me/submissions/01d50230-6984-4fbc-b9e8-89130d083595

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
theorem _root_.solution {J : Ideal (MRing ι)} (hp : ((p : ℕ) : MRing ι) ∈ J) (g : MRing ι) :
    red p g ∈ J.map (red p) ↔ g ∈ J := by
  rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective _ (red_surjective p), sup_eq_left.mpr]
  rw [← RingHom.ker_eq_comap_bot]
  exact ker_red_le p hp
end GroundTheory.Heights₂.Heights.Inter.PointVertical

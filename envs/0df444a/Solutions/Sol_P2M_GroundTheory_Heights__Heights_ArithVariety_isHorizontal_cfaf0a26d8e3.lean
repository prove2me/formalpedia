-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ArithVariety_isHorizontal_cfaf0a26d8e3
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:52:12.985799+00:00
-- url     : https://prove2.me/submissions/8276baaa-e22f-4a9f-b007-38cf0cac02a1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_RationalSections_IsRatSectionOn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightObjects

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
open scoped ContDiff
noncomputable section
variable {ι : Type} {n : ι → ℕ}
variable [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights
namespace ArithVariety
theorem _root_.solution (P : ArithVariety n) :
    Geo.IsHorizontal (ι := blockIdx n) P.ideal := by
  ext a
  rw [Ideal.mem_comap, Ideal.mem_bot]
  exact ⟨P.horizontal a, fun h ↦ by rw [h, map_zero]; exact P.ideal.zero_mem⟩
end ArithVariety
end GroundTheory.Heights₂.Heights

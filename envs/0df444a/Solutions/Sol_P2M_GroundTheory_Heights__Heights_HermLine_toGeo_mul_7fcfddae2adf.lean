-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HermLine_toGeo_mul_7fcfddae2adf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:05:55.46948+00:00
-- url     : https://prove2.me/submissions/d14039d0-9ad6-4630-9e12-1a1662fb86f6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_RationalSections_IsRatSectionOn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightObjects
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermLine_geo_ext_23b8d9aa88c8

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
open GroundTheory.Heights₂.Heights.HermLine
namespace GroundTheory.Heights₂.Heights.HermLine
theorem _root_.solution (A B : HermLine n) : (A.mul B).toGeo = A.toGeo.tensor B.toGeo := by
  refine geo_ext rfl ?_
  funext w
  simp only [toGeo, mul, Geo.HermLine.tensor]
  split_ifs <;> simp
end GroundTheory.Heights₂.Heights.HermLine

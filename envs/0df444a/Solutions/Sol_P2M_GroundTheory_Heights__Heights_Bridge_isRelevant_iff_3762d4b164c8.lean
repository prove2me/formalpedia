-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Bridge_isRelevant_iff_3762d4b164c8
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:34:29.621324+00:00
-- url     : https://prove2.me/submissions/e48b26ed-fa93-4ba1-87a1-3cd98d156952

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Bridge
open MvPolynomial
noncomputable section
variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
namespace GroundTheory.Heights₂.Heights.Bridge
theorem _root_.solution (W : Ideal (NumbersDVR.MRing ι R)) :
    NumbersDVR.IsRelevant W ↔ ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant (R := R) W := Iff.rfl
end GroundTheory.Heights₂.Heights.Bridge

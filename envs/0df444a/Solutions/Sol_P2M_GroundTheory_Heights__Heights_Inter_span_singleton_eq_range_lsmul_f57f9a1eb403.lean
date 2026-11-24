-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_span_singleton_eq_range_lsmul_f57f9a1eb403
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:38.003199+00:00
-- url     : https://prove2.me/submissions/cfa367b6-b465-4ab9-ba7a-3379ade71064

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerSide
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerExtra
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_CardLength
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_KrullDimQuotientEqOneIffEqBot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_SpanSingletonEqRangeLsmul

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
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution {A : Type*} [CommRing A] (x : A) :
    Ideal.span {x} = LinearMap.range (LinearMap.lsmul A A x) := by
  ext z
  simp [Ideal.mem_span_singleton', LinearMap.mem_range, mul_comm]
end GroundTheory.Heights₂.Heights.Inter

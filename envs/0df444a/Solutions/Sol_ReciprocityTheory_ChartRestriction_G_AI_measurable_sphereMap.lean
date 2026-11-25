-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.measurable_sphereMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:31:19.363822+00:00
-- url     : https://prove2.me/submissions/1d42015c-dace-4fc0-99c5-749ed1da87bf

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_KappaSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_KappaA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open scoped Pointwise
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI
namespace ReciprocityTheory.ChartRestriction.G.AI
theorem _root_.solution (L : E3 ≃ₗᵢ[ℝ] E3) :
    Measurable (fun n : S2 => (⟨L n, by simp⟩ : S2)) := ((L.continuous.comp continuous_subtype_val).subtype_mk _).measurable
end ReciprocityTheory.ChartRestriction.G.AI

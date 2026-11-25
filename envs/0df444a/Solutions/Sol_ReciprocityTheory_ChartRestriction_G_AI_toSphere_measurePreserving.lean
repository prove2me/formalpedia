-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.toSphere_measurePreserving
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:43:36.065034+00:00
-- url     : https://prove2.me/submissions/c700d58c-70db-4b20-81ba-ac83806993b1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_KappaSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_KappaA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_cone_preimage
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_measurable_sphereMap

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
    MeasurePreserving (fun n : S2 => (⟨L n, by simp⟩ : S2))
      (volume : Measure E3).toSphere (volume : Measure E3).toSphere := by
  refine ⟨measurable_sphereMap L, ?_⟩
  ext s hs
  rw [Measure.map_apply (measurable_sphereMap L) hs, Measure.toSphere_apply' _ hs,
    Measure.toSphere_apply' _ (measurable_sphereMap L hs), cone_preimage]
  congr 1
  have hmp : MeasurePreserving (L.toHomeomorph.toMeasurableEquiv) (volume : Measure E3) volume :=
    L.measurePreserving
  exact hmp.measure_preimage_equiv _
end ReciprocityTheory.ChartRestriction.G.AI

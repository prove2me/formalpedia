-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.integral_sphere_isometry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:57:51.971374+00:00
-- url     : https://prove2.me/submissions/20a797d4-698e-4111-9d26-74a0e84948c2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LintegralIoiOfRealMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_KappaB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_sphereInv_thm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI
open MeasureTheory
namespace ReciprocityTheory.ChartRestriction.G.AI
theorem _root_.solution (L : E3 ≃ₗᵢ[ℝ] E3) (F : E3 → ℝ)
    (hF : Integrable (fun n : S2 => F n) sphereMeasure) :
    ∫ n : S2, F (L n) ∂sphereMeasure = ∫ n : S2, F n ∂sphereMeasure := by
  have hinv := sphereInv_thm
  unfold SphereInvStatement at hinv
  have hmp := hinv.2 L
  have h := integral_map (μ := sphereMeasure) hmp.measurable.aemeasurable
    (f := fun m : S2 => F (m : E3)) (by rw [hmp.map_eq]; exact hF.aestronglyMeasurable)
  rw [hmp.map_eq] at h
  exact h.symm
end ReciprocityTheory.ChartRestriction.G.AI

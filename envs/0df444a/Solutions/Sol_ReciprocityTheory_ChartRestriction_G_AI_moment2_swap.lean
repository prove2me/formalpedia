-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.moment2_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:09:17.8851+00:00
-- url     : https://prove2.me/submissions/29f6e660-a11e-47b8-99e4-209a347ec4dd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LintegralIoiOfRealMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_KappaB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_moment2_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_reflection_fix

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
variable {u : E3} {f : ℝ → ℝ}
namespace ReciprocityTheory.ChartRestriction.G.AI
theorem _root_.solution (hI : Integrable (fun n : S2 => f (inner ℝ (n : E3) u)) sphereMeasure)
    {a c : E3} (ha : inner ℝ a u = 0) (hc : inner ℝ c u = 0) (hac : ‖a‖ = ‖c‖) :
    ∫ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) c * inner ℝ (n : E3) c ∂sphereMeasure =
      ∫ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) a * inner ℝ (n : E3) a
        ∂sphereMeasure := by
  have hdu : inner ℝ (a - c) u = 0 := by rw [inner_sub_left, ha, hc, sub_zero]
  have hRu : (ℝ ∙ (a - c))ᗮ.reflection u = u := reflection_fix hdu
  have hRa : (ℝ ∙ (a - c))ᗮ.reflection a = c := Submodule.reflection_sub hac
  have h := moment2_inv hI ((ℝ ∙ (a - c))ᗮ.reflection) hRu a a
  rw [hRa] at h
  exact h
end ReciprocityTheory.ChartRestriction.G.AI

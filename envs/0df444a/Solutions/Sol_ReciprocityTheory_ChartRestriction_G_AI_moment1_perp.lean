-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.moment1_perp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:09:08.012637+00:00
-- url     : https://prove2.me/submissions/88e6b100-71aa-4658-84bb-9360a396460c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LintegralIoiOfRealMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_KappaB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_moment1_inv
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
    {a : E3} (ha : inner ℝ a u = 0) :
    ∫ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) a ∂sphereMeasure = 0 := by
  have hRu : (ℝ ∙ a)ᗮ.reflection u = u := reflection_fix ha
  have hRa : (ℝ ∙ a)ᗮ.reflection a = -a :=
    Submodule.reflection_orthogonalComplement_singleton_eq_neg a
  have h := moment1_inv hI ((ℝ ∙ a)ᗮ.reflection) hRu a
  rw [hRa] at h
  simp only [inner_neg_right, mul_neg, integral_neg] at h
  linarith
end ReciprocityTheory.ChartRestriction.G.AI

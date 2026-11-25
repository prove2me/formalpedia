-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.moment2_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:02:32.20644+00:00
-- url     : https://prove2.me/submissions/46212b04-977e-4cc5-8f99-ac5c707a2d99

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LintegralIoiOfRealMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_KappaB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_integral_sphere_isometry
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_integrable_mul_inner

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
    (L : E3 ≃ₗᵢ[ℝ] E3) (hL : L u = u) (v w : E3) :
    ∫ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) (L v) * inner ℝ (n : E3) (L w)
        ∂sphereMeasure =
      ∫ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) v * inner ℝ (n : E3) w
        ∂sphereMeasure := by
  have key : ∀ x y : E3, inner ℝ (L.symm x) y = inner ℝ x (L y) := by
    intro x y
    rw [← L.inner_map_map (L.symm x) y, L.apply_symm_apply]
  have h := integral_sphere_isometry L.symm (fun x => f (inner ℝ x u) * inner ℝ x v * inner ℝ x w)
    (integrable_mul_inner (integrable_mul_inner hI v) w)
  simp only [key, hL] at h
  exact h
end ReciprocityTheory.ChartRestriction.G.AI

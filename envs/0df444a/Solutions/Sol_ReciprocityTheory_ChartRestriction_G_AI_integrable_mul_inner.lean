-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.integrable_mul_inner
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:53:15.870041+00:00
-- url     : https://prove2.me/submissions/84df9ae3-7ec1-4d7e-991e-55edc986804e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LintegralIoiOfRealMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_KappaB

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
theorem _root_.solution {F : S2 → ℝ} (hF : Integrable F sphereMeasure) (v : E3) :
    Integrable (fun n : S2 => F n * inner ℝ (n : E3) v) sphereMeasure := by
  have hc : Continuous (fun n : S2 => inner ℝ (n : E3) v) :=
    continuous_subtype_val.inner continuous_const
  refine Integrable.mono' (hF.norm.mul_const ‖v‖)
    (hF.aestronglyMeasurable.mul hc.aestronglyMeasurable) (ae_of_all _ fun n => ?_)
  have hn : ‖(n : E3)‖ = 1 := norm_eq_of_mem_sphere n
  have hb : |inner ℝ (n : E3) v| ≤ ‖v‖ := by
    calc |inner ℝ (n : E3) v| ≤ ‖(n : E3)‖ * ‖v‖ := abs_real_inner_le_norm _ _
      _ = ‖v‖ := by rw [hn, one_mul]
  rw [norm_mul, Real.norm_eq_abs (inner ℝ (n : E3) v)]
  exact mul_le_mul_of_nonneg_left hb (norm_nonneg _)
end ReciprocityTheory.ChartRestriction.G.AI

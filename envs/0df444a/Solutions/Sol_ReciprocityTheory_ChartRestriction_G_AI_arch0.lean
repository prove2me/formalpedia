-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.arch0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:04:43.36495+00:00
-- url     : https://prove2.me/submissions/606647ba-2864-4d06-9f91-ab1119e8831e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_KappaA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LintegralIoiOfRealMul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_ArchimedeanConeVolume_map_inner_sphereMeasure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Real
open scoped ENNReal Pointwise
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI
open ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume
namespace ReciprocityTheory.ChartRestriction.G.AI
theorem _root_.solution (u : E3) (f : ℝ → ℝ) (hu : ‖u‖ = 1) (hf : IntervalIntegrable f MeasureTheory.volume (-1) 1) :
    MeasureTheory.Integrable (fun n : S2 => f (inner ℝ (n : E3) u)) sphereMeasure ∧
    ∫ n : S2, f (inner ℝ (n : E3) u) ∂sphereMeasure = (1 / 2) * ∫ t in (-1 : ℝ)..1, f t := by
  have hφ : Measurable (fun n : S2 => inner ℝ (n : E3) u) := by fun_prop
  have hmap := map_inner_sphereMeasure hu
  have hIoo : IntegrableOn f (Ioo (-1 : ℝ) 1) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).1 hf).mono_set Ioo_subset_Ioc_self
  have hint : Integrable f ((2⁻¹ : ℝ≥0∞) • volume.restrict (Ioo (-1 : ℝ) 1)) :=
    hIoo.smul_measure (by simp)
  rw [← hmap] at hint
  refine ⟨(integrable_map_measure hint.aestronglyMeasurable hφ.aemeasurable).1 hint, ?_⟩
  rw [← integral_map hφ.aemeasurable hint.aestronglyMeasurable, hmap, integral_smul_measure,
    intervalIntegral.integral_of_le (by norm_num), integral_Ioc_eq_integral_Ioo]
  simp
end ReciprocityTheory.ChartRestriction.G.AI

-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume.lintegral_cylindrical
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:28:37.15053+00:00
-- url     : https://prove2.me/submissions/aa2fe925-7c9e-4349-87e4-14f8513f3f23

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_KappaA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LintegralIoiOfRealMul

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume
namespace ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume
theorem _root_.solution (H : ℝ × (ℝ × ℝ) → ℝ≥0∞) (hH : Measurable H) :
    ∫⁻ x : E3, H (x 0, (x 1, x 2)) = ∫⁻ z : ℝ, ∫⁻ p : ℝ × ℝ, H (z, p) := by
  have hΦ : MeasurePreserving (fun x : E3 => (x 0, (x 1, x 2))) volume volume := by
    have h1 := PiLp.volume_preserving_ofLp (Fin 3)
    have h2 := volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0
    have h3 := (MeasurePreserving.id (volume : Measure ℝ)).prod
      (volume_preserving_finTwoArrow ℝ)
    have := h3.comp (h2.comp h1)
    have hf : (fun x : E3 => (x 0, (x 1, x 2))) = Prod.map id MeasurableEquiv.finTwoArrow ∘
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0) ∘ WithLp.ofLp := by
      funext x; rfl
    rw [hf, Measure.volume_eq_prod]
    exact this
  rw [hΦ.lintegral_comp hH, Measure.volume_eq_prod, lintegral_prod _ hH.aemeasurable]
end ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume

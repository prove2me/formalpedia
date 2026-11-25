-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.J2.lint_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:17:22.535674+00:00
-- url     : https://prove2.me/submissions/b67aaf0e-379a-42bf-a90d-d74f2d8a6420

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GaugeSplittingAlgebra
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_VolumeUnivFinZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Module
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.J2
namespace ReciprocityTheory.ChartRestriction.DS.Xi.J2
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → ℝ≥0∞} (hf : Measurable f)
    {t : ℝ} (ht : t ≠ 0) :
    ∫⁻ x, f (t • x) ∂μ = ENNReal.ofReal |(t ^ finrank ℝ E)⁻¹| * ∫⁻ x, f x ∂μ := by
  have hdet : LinearMap.det (t • LinearMap.id : E →ₗ[ℝ] E) = t ^ finrank ℝ E := by
    rw [LinearMap.det_smul, LinearMap.det_id, mul_one]
  have hne : LinearMap.det (t • LinearMap.id : E →ₗ[ℝ] E) ≠ 0 := by
    rw [hdet]
    exact pow_ne_zero _ ht
  have hmap := MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar μ hne
  have hf' : (fun x => f (t • x)) = fun x => f ((t • LinearMap.id : E →ₗ[ℝ] E) x) := rfl
  rw [hf', ← MeasureTheory.lintegral_map hf (LinearMap.continuous_of_finiteDimensional _).measurable, hmap,
    MeasureTheory.lintegral_smul_measure, hdet, smul_eq_mul]
end ReciprocityTheory.ChartRestriction.DS.Xi.J2

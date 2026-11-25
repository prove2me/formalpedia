-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Laplace.gauss_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:25:48.107731+00:00
-- url     : https://prove2.me/submissions/f087850d-999d-4d4e-9f74-8838143b18d8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_Laplace
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Laplace_gauss_diag
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Laplace_exists_diag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex Filter Topology Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.Laplace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Laplace
theorem _root_.solution (μ : Measure E) [μ.IsAddHaarMeasure] (B : E →ₗ[ℝ] E →ₗ[ℝ] ℂ)
    (hB : ∀ v, v ≠ 0 → 0 < (B v v).re) : ∫ v, cexp (-(B v v)) ∂μ ≠ 0 := by
  obtain ⟨L, b, hb, hL⟩ := exists_diag B hB
  have hemb : MeasurableEmbedding
      (L.toContinuousLinearEquiv : (Fin (Module.finrank ℝ E) → ℝ) → E) :=
    L.toContinuousLinearEquiv.toHomeomorph.measurableEmbedding
  have hμ : μ = Measure.addHaarScalarFactor μ
      (Measure.map (L.toContinuousLinearEquiv : (Fin (Module.finrank ℝ E) → ℝ) → E) volume) •
      Measure.map (L.toContinuousLinearEquiv : (Fin (Module.finrank ℝ E) → ℝ) → E) volume := by
    apply Measure.isAddLeftInvariant_eq_smul
  have hc : 0 < Measure.addHaarScalarFactor μ
      (Measure.map (L.toContinuousLinearEquiv : (Fin (Module.finrank ℝ E) → ℝ) → E) volume) := by
    apply Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure
  have h2 : ∀ w : Fin (Module.finrank ℝ E) → ℝ,
      cexp (-(B (L.toContinuousLinearEquiv w) (L.toContinuousLinearEquiv w))) =
        cexp (-∑ i, b i * (w i : ℂ) ^ 2) := by
    intro w
    rw [show L.toContinuousLinearEquiv w = L w from rfl, hL]
  rw [hμ, integral_smul_nnreal_measure, hemb.integral_map]
  simp_rw [h2]
  rw [NNReal.smul_def, Complex.real_smul]
  exact mul_ne_zero (Complex.ofReal_ne_zero.2 (NNReal.coe_pos.2 hc).ne') (gauss_diag b hb)
end ReciprocityTheory.ChartRestriction.DS.Lap.Laplace

-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.OntoG.I_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:24:52.556851+00:00
-- url     : https://prove2.me/submissions/2c16bc38-3f1f-4043-97b2-35d2bf57257b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfG
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_OntoG_amgm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.OntoG
open MeasureTheory
open scoped ENNReal ComplexConjugate
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OntoG
theorem _root_.solution {α : Type*} [MeasurableSpace α] {μ : Measure α} {k : α → ℝ} {g u : α → ℂ}
    {w : α → ℝ≥0∞} {q : ℝ} (hk : ∀ᵐ a ∂μ, 0 < k a) (hw : ∀ᵐ a ∂μ, w a < ⊤) (hq1 : q < 1)
    (hq0 : 0 ≤ q) (hkm : AEMeasurable k μ) (hgm : AEMeasurable g μ) (hum : AEMeasurable u μ)
    (hwm : AEMeasurable w μ)
    (hI : ∫⁻ a, ENNReal.ofReal (k a * ‖g a‖ ^ 2) * w a ∂μ < ⊤)
    (hJ : ∫⁻ a, ENNReal.ofReal (‖u a‖ ^ 2 / k a) * w a ∂μ ≤
      ENNReal.ofReal q * ∫⁻ a, ENNReal.ofReal (k a * ‖g a‖ ^ 2) * w a ∂μ)
    (h0 : ∫ a, ((k a : ℂ) * g a - u a) * conj (g a) * ((w a).toReal : ℂ) ∂μ = 0) :
    ∫⁻ a, ENNReal.ofReal (k a * ‖g a‖ ^ 2) * w a ∂μ = 0 := by
  have hWm : AEMeasurable (fun a => (w a).toReal) μ := hwm.ennreal_toReal
  have hF1m : AEMeasurable (fun a => k a * ‖g a‖ ^ 2 * (w a).toReal) μ :=
    (hkm.mul (hgm.norm.pow_const 2)).mul hWm
  have hF2m : AEMeasurable (fun a => ‖u a‖ ^ 2 / k a * (w a).toReal) μ :=
    ((hum.norm.pow_const 2).div hkm).mul hWm
  have hF1nn : 0 ≤ᵐ[μ] fun a => k a * ‖g a‖ ^ 2 * (w a).toReal := by
    filter_upwards [hk] with a ha
    exact mul_nonneg (mul_nonneg ha.le (sq_nonneg _)) ENNReal.toReal_nonneg
  have hF2nn : 0 ≤ᵐ[μ] fun a => ‖u a‖ ^ 2 / k a * (w a).toReal := by
    filter_upwards [hk] with a ha
    exact mul_nonneg (div_nonneg (sq_nonneg _) ha.le) ENNReal.toReal_nonneg
  have hA : ∫⁻ a, ENNReal.ofReal (k a * ‖g a‖ ^ 2) * w a ∂μ =
      ∫⁻ a, ENNReal.ofReal (k a * ‖g a‖ ^ 2 * (w a).toReal) ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hk, hw] with a ha hwa
    rw [ENNReal.ofReal_mul (mul_nonneg ha.le (sq_nonneg _)), ENNReal.ofReal_toReal hwa.ne]
  have hB : ∫⁻ a, ENNReal.ofReal (‖u a‖ ^ 2 / k a) * w a ∂μ =
      ∫⁻ a, ENNReal.ofReal (‖u a‖ ^ 2 / k a * (w a).toReal) ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hk, hw] with a ha hwa
    rw [ENNReal.ofReal_mul (div_nonneg (sq_nonneg _) ha.le), ENNReal.ofReal_toReal hwa.ne]
  rw [hA] at hI hJ ⊢
  rw [hB] at hJ
  have hJfin : ∫⁻ a, ENNReal.ofReal (‖u a‖ ^ 2 / k a * (w a).toReal) ∂μ < ⊤ :=
    lt_of_le_of_lt hJ (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hI)
  have hF1i : Integrable (fun a => k a * ‖g a‖ ^ 2 * (w a).toReal) μ :=
    ⟨hF1m.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hF1nn).2 hI⟩
  have hF2i : Integrable (fun a => ‖u a‖ ^ 2 / k a * (w a).toReal) μ :=
    ⟨hF2m.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hF2nn).2 hJfin⟩
  have hint1 : ∫ a, k a * ‖g a‖ ^ 2 * (w a).toReal ∂μ =
      (∫⁻ a, ENNReal.ofReal (k a * ‖g a‖ ^ 2 * (w a).toReal) ∂μ).toReal :=
    integral_eq_lintegral_of_nonneg_ae hF1nn hF1m.aestronglyMeasurable
  have hint2 : ∫ a, ‖u a‖ ^ 2 / k a * (w a).toReal ∂μ =
      (∫⁻ a, ENNReal.ofReal (‖u a‖ ^ 2 / k a * (w a).toReal) ∂μ).toReal :=
    integral_eq_lintegral_of_nonneg_ae hF2nn hF2m.aestronglyMeasurable
  have hPm : AEStronglyMeasurable (fun a => u a * conj (g a) * ((w a).toReal : ℂ)) μ :=
    ((hum.mul (Complex.continuous_conj.measurable.comp_aemeasurable hgm)).mul
      (Complex.measurable_ofReal.comp_aemeasurable hWm)).aestronglyMeasurable
  have hPbd : ∀ᵐ a ∂μ, ‖u a * conj (g a) * ((w a).toReal : ℂ)‖ ≤
      (‖u a‖ ^ 2 / k a * (w a).toReal + k a * ‖g a‖ ^ 2 * (w a).toReal) / 2 := by
    filter_upwards [hk] with a ha
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ENNReal.toReal_nonneg]
    have h1 := amgm (k := k a) (x := ‖u a‖) (y := ‖g a‖) ha
    have hW0 : 0 ≤ (w a).toReal := ENNReal.toReal_nonneg
    nlinarith [mul_le_mul_of_nonneg_right h1 hW0]
  have hbdi : Integrable (fun a => (‖u a‖ ^ 2 / k a * (w a).toReal + k a * ‖g a‖ ^ 2 * (w a).toReal) / 2) μ :=
    (hF2i.add hF1i).div_const 2
  have hPi : Integrable (fun a => u a * conj (g a) * ((w a).toReal : ℂ)) μ :=
    Integrable.mono' hbdi hPm hPbd
  have hF1c : Integrable (fun a => ((k a * ‖g a‖ ^ 2 * (w a).toReal : ℝ) : ℂ)) μ := hF1i.ofReal
  have hsplit : (fun a => ((k a : ℂ) * g a - u a) * conj (g a) * ((w a).toReal : ℂ)) =
      fun a => ((k a * ‖g a‖ ^ 2 * (w a).toReal : ℝ) : ℂ) - u a * conj (g a) * ((w a).toReal : ℂ) := by
    funext a
    rw [sub_mul, sub_mul, mul_assoc (k a : ℂ) (g a) (conj (g a)), Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
    push_cast
    ring
  rw [hsplit, integral_sub hF1c hPi, integral_complex_ofReal, sub_eq_zero] at h0
  have hn : 0 ≤ ∫ a, k a * ‖g a‖ ^ 2 * (w a).toReal ∂μ := integral_nonneg_of_ae hF1nn
  have hle : ∫ a, k a * ‖g a‖ ^ 2 * (w a).toReal ∂μ ≤
      ((∫ a, ‖u a‖ ^ 2 / k a * (w a).toReal ∂μ) + ∫ a, k a * ‖g a‖ ^ 2 * (w a).toReal ∂μ) / 2 := by
    calc ∫ a, k a * ‖g a‖ ^ 2 * (w a).toReal ∂μ
        = ‖((∫ a, k a * ‖g a‖ ^ 2 * (w a).toReal ∂μ : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_of_nonneg hn]
      _ = ‖∫ a, u a * conj (g a) * ((w a).toReal : ℂ) ∂μ‖ := by rw [h0]
      _ ≤ ∫ a, ‖u a * conj (g a) * ((w a).toReal : ℂ)‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ a, (‖u a‖ ^ 2 / k a * (w a).toReal + k a * ‖g a‖ ^ 2 * (w a).toReal) / 2 ∂μ :=
          integral_mono_ae hPi.norm hbdi hPbd
      _ = ((∫ a, ‖u a‖ ^ 2 / k a * (w a).toReal ∂μ) + ∫ a, k a * ‖g a‖ ^ 2 * (w a).toReal ∂μ) / 2 := by
          rw [integral_div, integral_add hF2i hF1i]
  have hJr : ∫ a, ‖u a‖ ^ 2 / k a * (w a).toReal ∂μ ≤ q * ∫ a, k a * ‖g a‖ ^ 2 * (w a).toReal ∂μ := by
    rw [hint1, hint2]
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI.ne) hJ
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hq0] at this
  have hz : ∫ a, k a * ‖g a‖ ^ 2 * (w a).toReal ∂μ = 0 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hq1.le) hn]
  rw [hint1] at hz
  exact ((ENNReal.toReal_eq_zero_iff _).1 hz).resolve_right hI.ne
end ReciprocityTheory.ChartRestriction.G.AR.Up.OntoG

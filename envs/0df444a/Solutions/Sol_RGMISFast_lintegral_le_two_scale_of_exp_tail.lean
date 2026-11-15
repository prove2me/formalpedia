-- Prove2me | solution 1 for RGMISFast.lintegral_le_two_scale_of_exp_tail
-- status  : ACCEPTED   (prove)
-- author  : @srikkanthr
-- created : 2026-11-15T00:59:59.45221+00:00
-- url     : https://prove2.me/submissions/e10f0942-292d-41dd-ad95-13a619fd6912

import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic
open MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℕ) (hX : Measurable X)
    (F : ℝ) (hF : 0 < F)
    (htail : ∀ h : ℝ, 0 ≤ h → μ {ω | F * (1 + h) < (X ω : ℝ)} ≤
      ENNReal.ofReal (Real.exp (-h))) :
    ∫⁻ ω, (X ω : ℝ≥0∞) ∂μ ≤ ENNReal.ofReal (2 * F) := by
  let Y : Ω → ℝ := fun ω => max ((X ω : ℝ) / F - 1) 0
  have hm : Measurable Y := ((((measurable_of_countable _ : Measurable (fun n : ℕ => (n : ℝ))).comp hX).div_const F).sub measurable_const).max measurable_const
  have hn : ∀ ω, 0 ≤ Y ω := fun _ => le_max_right _ _
  have hy : ∫⁻ ω, ENNReal.ofReal (Y ω) ∂μ ≤ 1 := by
    rw [lintegral_eq_lintegral_meas_lt μ (Filter.Eventually.of_forall hn) hm.aemeasurable]
    calc
      _ ≤ ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-t)) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have htpos : 0 < t := ht
        have hs : {ω | t < Y ω} = {ω | F * (1 + t) < (X ω : ℝ)} := by
          ext ω
          simp only [mem_setOf_eq, Y, lt_max_iff, not_lt_of_ge htpos.le, or_false]
          rw [lt_sub_iff_add_lt, lt_div_iff₀ hF]
          ring_nf
        rw [hs]
        exact htail t htpos.le
      _ = 1 := by
        rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_neg_Ioi 0)
          (Filter.Eventually.of_forall (fun t => (Real.exp_pos (-t)).le)), integral_exp_neg_Ioi_zero]
        simp
  have hp : ∀ ω, (X ω : ℝ) ≤ F + F * Y ω := by
    intro ω
    have hs := mul_le_mul_of_nonneg_left (le_max_left ((X ω : ℝ) / F - 1) 0) hF.le
    have hc : F * ((X ω : ℝ) / F) = X ω := by field_simp
    dsimp [Y]
    nlinarith
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal (F + F * Y ω) ∂μ := by
      apply lintegral_mono
      intro ω
      simpa using ENNReal.ofReal_le_ofReal (hp ω)
    _ = ENNReal.ofReal F + ENNReal.ofReal F * ∫⁻ ω, ENNReal.ofReal (Y ω) ∂μ := by
      simp_rw [ENNReal.ofReal_add hF.le (mul_nonneg hF.le (hn _)), ENNReal.ofReal_mul hF.le]
      rw [lintegral_add_left measurable_const, lintegral_const_mul _ (hm.ennreal_ofReal)]
      simp
    _ ≤ ENNReal.ofReal F + ENNReal.ofReal F * 1 := by gcongr
    _ = ENNReal.ofReal (2 * F) := by
      rw [mul_one, ← ENNReal.ofReal_add hF.le hF.le]
      congr 1
      ring

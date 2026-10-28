-- Prove2me | solution 1 for SmoothAmbEq.Gaussian.lemma_C_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T19:03:20.389193+00:00
-- url     : https://prove2.me/submissions/6f77ed47-8f66-4a23-a163-18bf3503b231

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SAEC2

/-- Completing the square: the Gaussian density times `exp(a x² + b x)`. -/
lemma pdf_mul_exp (μ a b V x : ℝ) (hV : 0 < V) (hs : 1 - 2 * a * V ≠ 0) :
    (Real.sqrt (2 * Real.pi * V))⁻¹ * Real.exp (-(x - μ) ^ 2 / (2 * V)) *
        Real.exp (a * x ^ 2 + b * x)
      = ((Real.sqrt (2 * Real.pi * V))⁻¹ *
          Real.exp ((2 * a * μ ^ 2 + 2 * μ * b + b ^ 2 * V) / (2 * (1 - 2 * a * V)))) *
        Real.exp (-((1 - 2 * a * V) / (2 * V)) * (x - (μ + b * V) / (1 - 2 * a * V)) ^ 2) := by
  simp only [mul_assoc, ← Real.exp_add]
  congr 2
  have ha : a = (1 - (1 - 2 * a * V)) / (2 * V) := by field_simp; ring
  generalize 1 - 2 * a * V = s at *
  subst ha
  have hV' : V ≠ 0 := hV.ne'
  have e : 1 - 2 * ((1 - s) / (2 * V) * V) = s := by field_simp; ring
  rw [e]
  field_simp
  ring

lemma integral_odd (A : ℝ) : ∫ y : ℝ, y * Real.exp (-A * y ^ 2) = 0 := by
  have h := integral_neg_eq_self (fun y : ℝ => y * Real.exp (-A * y ^ 2)) volume
  simp only [neg_mul, even_two, Even.neg_pow, integral_neg] at h ⊢
  linarith

end SAEC2

open SAEC2

theorem solution (μ a b : ℝ) (v : ℝ≥0) :
    (2 * a * v < 1 →
      (∫⁻ ξ, ENNReal.ofReal (Real.exp (a * ξ ^ 2 + b * ξ)) ∂(gaussianReal μ v)) =
          ENNReal.ofReal (1 / Real.sqrt (1 - 2 * a * v) *
            Real.exp ((2 * a * μ ^ 2 + 2 * μ * b + b ^ 2 * v) / (2 * (1 - 2 * a * v)))) ∧
        Integrable (fun ξ => ξ * Real.exp (a * ξ ^ 2 + b * ξ)) (gaussianReal μ v) ∧
        ∫ ξ, ξ * Real.exp (a * ξ ^ 2 + b * ξ) ∂(gaussianReal μ v) =
          (μ + b * v) / (1 - 2 * a * v) ^ ((3 : ℝ) / 2) *
            Real.exp ((2 * a * μ ^ 2 + 2 * μ * b + b ^ 2 * v) / (2 * (1 - 2 * a * v)))) ∧
    (1 ≤ 2 * a * v →
      (∫⁻ ξ, ENNReal.ofReal (Real.exp (a * ξ ^ 2 + b * ξ)) ∂(gaussianReal μ v)) = ⊤) := by
  rcases eq_or_ne v 0 with hv | hv
  · -- degenerate variance: `gaussianReal μ 0 = δ_μ`
    subst hv
    refine ⟨fun _ => ⟨?_, ?_, ?_⟩, fun h => ?_⟩
    · simp only [gaussianReal_zero_var, lintegral_dirac, NNReal.coe_zero, mul_zero, sub_zero,
        Real.sqrt_one, div_one, add_zero, one_div, inv_one, one_mul]
      congr 2
      ring
    · simp only [gaussianReal_zero_var]
      exact integrable_dirac enorm_lt_top
    · simp only [gaussianReal_zero_var, integral_dirac, NNReal.coe_zero, mul_zero, sub_zero,
        add_zero, Real.one_rpow, div_one, mul_one]
      congr 2
      ring
    · simp at h; linarith
  -- positive variance
  set V : ℝ := (v : ℝ) with hVdef
  have hV : 0 < V := lt_of_le_of_ne v.2 (fun h => hv (by ext; simp [hVdef] at h ⊢; linarith))
  have hG : gaussianReal μ v = volume.withDensity (gaussianPDF μ v) :=
    gaussianReal_of_var_ne_zero μ hv
  -- the lintegral as a Lebesgue lintegral
  have hlin : (∫⁻ ξ, ENNReal.ofReal (Real.exp (a * ξ ^ 2 + b * ξ)) ∂(gaussianReal μ v)) =
      ∫⁻ ξ, ENNReal.ofReal ((Real.sqrt (2 * Real.pi * V))⁻¹ * Real.exp (-(ξ - μ) ^ 2 / (2 * V))
        * Real.exp (a * ξ ^ 2 + b * ξ)) := by
    rw [hG, lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF μ v)
      (by fun_prop)]
    congr 1; funext ξ
    simp only [Pi.mul_apply, gaussianPDF, gaussianPDFReal]
    rw [← ENNReal.ofReal_mul (by positivity)]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · set s : ℝ := 1 - 2 * a * V with hs_def
    have hs : 0 < s := by rw [hs_def]; linarith
    set A : ℝ := s / (2 * V) with hA_def
    have hA : 0 < A := by positivity
    set m : ℝ := (μ + b * V) / s with hm_def
    set K : ℝ := (Real.sqrt (2 * Real.pi * V))⁻¹ *
      Real.exp ((2 * a * μ ^ 2 + 2 * μ * b + b ^ 2 * V) / (2 * s)) with hK_def
    have hpt : ∀ ξ : ℝ, (Real.sqrt (2 * Real.pi * V))⁻¹ * Real.exp (-(ξ - μ) ^ 2 / (2 * V))
        * Real.exp (a * ξ ^ 2 + b * ξ) = K * Real.exp (-A * (ξ - m) ^ 2) := fun ξ =>
      pdf_mul_exp μ a b V ξ hV hs.ne'
    have hI0int : Integrable (fun ξ : ℝ => Real.exp (-A * (ξ - m) ^ 2)) :=
      (integrable_exp_neg_mul_sq hA).comp_sub_right m
    have hI0 : ∫ ξ : ℝ, Real.exp (-A * (ξ - m) ^ 2) = Real.sqrt (Real.pi / A) := by
      rw [integral_sub_right_eq_self (μ := volume) (fun ξ => Real.exp (-A * ξ ^ 2)) m]
      exact integral_gaussian A
    have hI1int : Integrable (fun ξ : ℝ => ξ * Real.exp (-A * (ξ - m) ^ 2)) := by
      have h1 := (integrable_mul_exp_neg_mul_sq hA).comp_sub_right m
      have h2 := hI0int.const_mul m
      refine (h1.add h2).congr (ae_of_all _ fun ξ => ?_)
      simp only [Pi.add_apply]; ring
    have hI1 : ∫ ξ : ℝ, ξ * Real.exp (-A * (ξ - m) ^ 2) = m * Real.sqrt (Real.pi / A) := by
      have h1 := (integrable_mul_exp_neg_mul_sq hA).comp_sub_right m
      have e : (fun ξ : ℝ => ξ * Real.exp (-A * (ξ - m) ^ 2)) =
          fun ξ => (ξ - m) * Real.exp (-A * (ξ - m) ^ 2) + m * Real.exp (-A * (ξ - m) ^ 2) := by
        funext ξ; ring
      rw [e, integral_add h1 (hI0int.const_mul m), integral_const_mul, hI0,
        integral_sub_right_eq_self (μ := volume) (fun ξ => ξ * Real.exp (-A * ξ ^ 2)) m,
        integral_odd, zero_add]
    -- normalising constant
    have hKc : K * Real.sqrt (Real.pi / A) = 1 / Real.sqrt s *
        Real.exp ((2 * a * μ ^ 2 + 2 * μ * b + b ^ 2 * V) / (2 * s)) := by
      have hpi := Real.pi_pos
      have e1 : Real.pi / A = (2 * Real.pi * V) / s := by
        rw [hA_def]; field_simp
      rw [hK_def, e1, Real.sqrt_div' _ hs.le]
      have : 0 < Real.sqrt (2 * Real.pi * V) := Real.sqrt_pos.2 (by positivity)
      have : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
      field_simp
    refine ⟨?_, ?_, ?_⟩
    · rw [hlin]
      simp_rw [hpt]
      rw [← ofReal_integral_eq_lintegral_ofReal (hI0int.const_mul K)
        (ae_of_all _ fun ξ => by positivity), integral_const_mul, hI0, hKc]
    · rw [hG, integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF μ v)
        (ae_of_all _ fun _ => gaussianPDF_lt_top)]
      refine (hI1int.const_mul K).congr (ae_of_all _ fun ξ => ?_)
      simp only [toReal_gaussianPDF, gaussianPDFReal, smul_eq_mul]
      rw [show K * (ξ * Real.exp (-A * (ξ - m) ^ 2)) = ξ * (K * Real.exp (-A * (ξ - m) ^ 2))
        by ring, ← hpt ξ]
      ring
    · rw [integral_gaussianReal_eq_integral_smul hv]
      have e : (fun ξ : ℝ => gaussianPDFReal μ v ξ • (ξ * Real.exp (a * ξ ^ 2 + b * ξ))) =
          fun ξ => K * (ξ * Real.exp (-A * (ξ - m) ^ 2)) := by
        funext ξ
        simp only [gaussianPDFReal, smul_eq_mul]
        rw [show K * (ξ * Real.exp (-A * (ξ - m) ^ 2)) = ξ * (K * Real.exp (-A * (ξ - m) ^ 2))
          by ring, ← hpt ξ]
        ring
      rw [e, integral_const_mul, hI1]
      have h32 : s ^ ((3 : ℝ) / 2) = s * Real.sqrt s := by
        rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hs, Real.rpow_one,
          Real.sqrt_eq_rpow]
      rw [h32, show K * (m * Real.sqrt (Real.pi / A)) = m * (K * Real.sqrt (Real.pi / A)) by ring,
        hKc, hm_def]
      have : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
      field_simp
  · -- divergent case
    rw [hlin]
    set B : ℝ := b + μ / V with hB
    set c0 : ℝ := -μ ^ 2 / (2 * V) with hc0
    set C : ℝ := (Real.sqrt (2 * Real.pi * V))⁻¹ * Real.exp c0 with hC
    have hCpos : 0 < C := by
      have : 0 < Real.sqrt (2 * Real.pi * V) := Real.sqrt_pos.2 (by positivity)
      positivity
    set S : Set ℝ := {ξ | 0 ≤ B * ξ} with hS
    have hSm : MeasurableSet S := measurableSet_le measurable_const (by fun_prop)
    have hSvol : volume S = ⊤ := by
      rcases le_total 0 B with hB0 | hB0
      · refine top_le_iff.1 ?_
        rw [← Real.volume_Ici (a := 0)]
        exact measure_mono fun ξ hξ => mul_nonneg hB0 hξ
      · refine top_le_iff.1 ?_
        rw [← Real.volume_Iic (a := 0)]
        exact measure_mono fun ξ (hξ : ξ ≤ 0) => mul_nonneg_of_nonpos_of_nonpos hB0 hξ
    have hlow : ∀ ξ, S.indicator (fun _ => ENNReal.ofReal C) ξ ≤
        ENNReal.ofReal ((Real.sqrt (2 * Real.pi * V))⁻¹ * Real.exp (-(ξ - μ) ^ 2 / (2 * V))
          * Real.exp (a * ξ ^ 2 + b * ξ)) := by
      intro ξ
      by_cases hξ : ξ ∈ S
      · rw [Set.indicator_of_mem hξ]
        apply ENNReal.ofReal_le_ofReal
        rw [hC, mul_assoc _ (Real.exp _) (Real.exp _), ← Real.exp_add]
        gcongr
        have hξ' : 0 ≤ B * ξ := hξ
        have e : -(ξ - μ) ^ 2 / (2 * V) + (a * ξ ^ 2 + b * ξ)
            = (2 * a * V - 1) / (2 * V) * ξ ^ 2 + B * ξ + c0 := by
          rw [hB, hc0]; field_simp; ring
        rw [e]
        have : 0 ≤ (2 * a * V - 1) / (2 * V) * ξ ^ 2 := by
          apply mul_nonneg _ (sq_nonneg _)
          apply div_nonneg _ (by positivity)
          have : (1 : ℝ) ≤ 2 * a * V := by simpa [hVdef] using h
          linarith
        linarith
      · rw [Set.indicator_of_notMem hξ]; exact zero_le
    refine top_le_iff.1 ?_
    calc (⊤ : ℝ≥0∞) = ENNReal.ofReal C * volume S := by
          rw [hSvol, ENNReal.mul_top (by simpa using hCpos)]
      _ = ∫⁻ ξ, S.indicator (fun _ => ENNReal.ofReal C) ξ := (lintegral_indicator_const hSm _).symm
      _ ≤ _ := lintegral_mono hlow

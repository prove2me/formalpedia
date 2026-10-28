-- Prove2me | solution 1 for avram_laplace_ae_eq_of_nonnegative_20261026
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T17:55:05.514486+00:00
-- url     : https://prove2.me/submissions/d44a5772-6754-444b-937c-edd27128c0d4

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_finiteMeasures_eq_of_complexMGF_eq_on_real_Iio
import Theorems.Thm_AvramDividend_Classical_ae_eq_Ioi_of_exponential_withDensity_eq
import Theorems.Thm_AvramDividend_Classical_psi_eventually_gt_of_standing
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology ProbabilityTheory
open scoped MeasureTheory ProbabilityTheory ENNReal NNReal Topology
open AvramDividend.Classical
theorem solution
    (f g : ℝ → ℝ) (b : ℝ)
    (hfnonneg : ∀ x : ℝ, 0 < x → 0 ≤ f x)
    (hgnonneg : ∀ x : ℝ, 0 < x → 0 ≤ g x)
    (hlap : ∀ θ : ℝ, b < θ →
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) * f x) (Ioi 0) ∧
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) * g x) (Ioi 0) ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * f x) =
        ∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * g x) :
    f =ᵐ[volume.restrict (Ioi (0 : ℝ))] g := by
  let μ0 : Measure ℝ := volume.restrict (Ioi 0)
  let B : ℝ := b + 1
  have hB : b < B := by dsimp [B]; linarith
  have hfB : Integrable (fun x : ℝ => Real.exp (-(B * x)) * f x) μ0 :=
    (hlap B hB).1.integrable
  have hgB : Integrable (fun x : ℝ => Real.exp (-(B * x)) * g x) μ0 :=
    (hlap B hB).2.1.integrable
  have hfdens : AEMeasurable
      (fun x : ℝ => ENNReal.ofReal (Real.exp (-(B * x)) * f x)) μ0 :=
    hfB.aemeasurable.ennreal_ofReal
  have hgdens : AEMeasurable
      (fun x : ℝ => ENNReal.ofReal (Real.exp (-(B * x)) * g x)) μ0 :=
    hgB.aemeasurable.ennreal_ofReal
  let μf : Measure ℝ := μ0.withDensity
    (fun x : ℝ => ENNReal.ofReal (Real.exp (-(B * x)) * f x))
  let μg : Measure ℝ := μ0.withDensity
    (fun x : ℝ => ENNReal.ofReal (Real.exp (-(B * x)) * g x))
  letI : IsFiniteMeasure μf := by
    dsimp [μf]
    exact isFiniteMeasure_withDensity_ofReal hfB.hasFiniteIntegral
  letI : IsFiniteMeasure μg := by
    dsimp [μg]
    exact isFiniteMeasure_withDensity_ofReal hgB.hasFiniteIntegral
  have hf_mgf_int (t : ℝ) (ht : t < 1) :
      Integrable (fun x : ℝ => Real.exp (t * x)) μf := by
    have hθ : b < B - t := by dsimp [B]; linarith
    have hbase : Integrable
        (fun x : ℝ => Real.exp (-((B - t) * x)) * f x) μ0 :=
      (hlap (B - t) hθ).1.integrable
    dsimp [μf]
    rw [integrable_withDensity_iff_integrable_smul₀' hfdens (by simp)]
    refine hbase.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hfx : 0 ≤ f x := hfnonneg x hx
    rw [ENNReal.toReal_ofReal (mul_nonneg (Real.exp_pos _).le hfx)]
    simp only [smul_eq_mul]
    calc
      Real.exp (-((B - t) * x)) * f x =
          (Real.exp (-(B * x)) * Real.exp (t * x)) * f x := by
            rw [← Real.exp_add]
            congr 2
            ring
      _ = (Real.exp (-(B * x)) * f x) * Real.exp (t * x) := by ring
  have hg_mgf_int (t : ℝ) (ht : t < 1) :
      Integrable (fun x : ℝ => Real.exp (t * x)) μg := by
    have hθ : b < B - t := by dsimp [B]; linarith
    have hbase : Integrable
        (fun x : ℝ => Real.exp (-((B - t) * x)) * g x) μ0 :=
      (hlap (B - t) hθ).2.1.integrable
    dsimp [μg]
    rw [integrable_withDensity_iff_integrable_smul₀' hgdens (by simp)]
    refine hbase.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hgx : 0 ≤ g x := hgnonneg x hx
    rw [ENNReal.toReal_ofReal (mul_nonneg (Real.exp_pos _).le hgx)]
    simp only [smul_eq_mul]
    calc
      Real.exp (-((B - t) * x)) * g x =
          (Real.exp (-(B * x)) * Real.exp (t * x)) * g x := by
            rw [← Real.exp_add]
            congr 2
            ring
      _ = (Real.exp (-(B * x)) * g x) * Real.exp (t * x) := by ring
  have hf_strip : Iio (1 : ℝ) ⊆ interior (integrableExpSet id μf) := by
    apply interior_maximal
    · intro t ht
      exact hf_mgf_int t ht
    · exact isOpen_Iio
  have hg_strip : Iio (1 : ℝ) ⊆ interior (integrableExpSet id μg) := by
    apply interior_maximal
    · intro t ht
      exact hg_mgf_int t ht
    · exact isOpen_Iio
  have hf_an :
      AnalyticOnNhd ℂ (complexMGF id μf) {z : ℂ | z.re < 1} :=
    analyticOnNhd_complexMGF.mono (fun z hz => hf_strip hz)
  have hg_an :
      AnalyticOnNhd ℂ (complexMGF id μg) {z : ℂ | z.re < 1} :=
    analyticOnNhd_complexMGF.mono (fun z hz => hg_strip hz)
  have hmgf_f (t : ℝ) (ht : t < 1) :
      mgf id μf t =
        ∫ x in Ioi (0 : ℝ), Real.exp (-((B - t) * x)) * f x := by
    rw [mgf]
    dsimp [μf]
    rw [integral_withDensity_eq_integral_toReal_smul₀ hfdens (by simp)]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hfx : 0 ≤ f x := hfnonneg x hx
    rw [ENNReal.toReal_ofReal (mul_nonneg (Real.exp_pos _).le hfx)]
    simp only [id_eq, smul_eq_mul]
    calc
      (Real.exp (-(B * x)) * f x) * Real.exp (t * x) =
          (Real.exp (-(B * x)) * Real.exp (t * x)) * f x := by ring
      _ = Real.exp (-((B - t) * x)) * f x := by
        rw [← Real.exp_add]
        congr 2
        ring
  have hmgf_g (t : ℝ) (ht : t < 1) :
      mgf id μg t =
        ∫ x in Ioi (0 : ℝ), Real.exp (-((B - t) * x)) * g x := by
    rw [mgf]
    dsimp [μg]
    rw [integral_withDensity_eq_integral_toReal_smul₀ hgdens (by simp)]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hgx : 0 ≤ g x := hgnonneg x hx
    rw [ENNReal.toReal_ofReal (mul_nonneg (Real.exp_pos _).le hgx)]
    simp only [id_eq, smul_eq_mul]
    calc
      (Real.exp (-(B * x)) * g x) * Real.exp (t * x) =
          (Real.exp (-(B * x)) * Real.exp (t * x)) * g x := by ring
      _ = Real.exp (-((B - t) * x)) * g x := by
        rw [← Real.exp_add]
        congr 2
        ring
  have hreal : ∀ t : ℝ, t < 1 →
      complexMGF id μf (t : ℂ) = complexMGF id μg (t : ℂ) := by
    intro t ht
    rw [complexMGF_ofReal, complexMGF_ofReal, hmgf_f t ht, hmgf_g t ht]
    exact congrArg (fun r : ℝ => (r : ℂ))
      (hlap (B - t) (by dsimp [B]; linarith)).2.2
  have hmeasure : μf = μg :=
    finiteMeasures_eq_of_complexMGF_eq_on_real_Iio
      μf μg 1 zero_lt_one hf_an hg_an hreal
  exact ae_eq_Ioi_of_exponential_withDensity_eq f g B hfnonneg hgnonneg
    (by simpa only [neg_mul, μ0] using hfdens) (by simpa only [neg_mul, μ0] using hgdens) (by simpa only [neg_mul, μ0, μf, μg] using hmeasure)

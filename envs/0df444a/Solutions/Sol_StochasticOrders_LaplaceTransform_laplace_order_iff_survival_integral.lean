-- Prove2me | solution 1 for StochasticOrders.LaplaceTransform.laplace_order_iff_survival_integral
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T09:32:39.2847+00:00
-- url     : https://prove2.me/submissions/81a20a55-b4a2-434f-89a7-c9f52a2e175d

import Mathlib
import Definitions.Def_StochasticOrders_LaplaceTransform_LaplaceOrder

set_option autoImplicit false

open MeasureTheory Filter Topology

theorem ltsurv_mean_integral_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X) (hXnn : ∀ ω, 0 ≤ X ω)
    (s : ℝ) (hs : 0 < s) :
    ∫ ω, (1 - Real.exp (-(s * X ω))) / s ∂μ = (1 - ∫ ω, Real.exp (-(s * X ω)) ∂μ) / s := by
  have hint : Integrable (fun ω => Real.exp (-(s * X ω))) μ := by
    refine Integrable.of_bound (C := 1) (by fun_prop) (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    have := hXnn ω; nlinarith
  rw [integral_div, integral_sub (integrable_const _) hint, integral_const]
  simp

theorem ltsurv_interval (s x : ℝ) (hs : 0 < s) :
    ∫ t in (0:ℝ)..x, Real.exp (-(s * t)) = (1 - Real.exp (-(s * x))) / s := by
  have hd : ∀ t ∈ Set.uIcc (0:ℝ) x,
      HasDerivAt (fun t : ℝ => -Real.exp (-(s * t)) / s) (Real.exp (-(s * t))) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => -(s * t)) (-s) t := by
      simpa using ((hasDerivAt_id t).const_mul s).fun_neg
    have h2 := (h1.exp.fun_neg).div_const s
    have e : -(Real.exp (-(s * t)) * -s) / s = Real.exp (-(s * t)) := by
      field_simp
    exact h2.congr_deriv e
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (by apply Continuous.intervalIntegrable; fun_prop)]
  simp only [mul_zero, neg_zero, Real.exp_zero]
  ring

theorem ltsurv_identity {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X) (hXnn : ∀ ω, 0 ≤ X ω)
    (s : ℝ) (hs : 0 < s) :
    ∫ x in Set.Ici (0 : ℝ), Real.exp (-(s * x)) * (μ {ω | x < X ω}).toReal =
      (1 - ∫ ω, Real.exp (-(s * X ω)) ∂μ) / s := by
  have layer := lintegral_comp_eq_lintegral_meas_lt_mul μ (f := X) (g := fun t => Real.exp (-(s * t)))
    (Eventually.of_forall hXnn) hX.aemeasurable
    (fun t _ => by apply Continuous.intervalIntegrable; fun_prop)
    (Eventually.of_forall fun t => (Real.exp_pos _).le)
  simp_rw [ltsurv_interval s _ hs] at layer
  have hanti : Antitone (fun x : ℝ => (μ {ω | x < X ω}).toReal) := by
    intro x y hxy
    exact ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_mono fun ω (hω : y < X ω) => lt_of_le_of_lt hxy hω)
  have hmeas : Measurable (fun x : ℝ => (μ {ω | x < X ω}).toReal) := hanti.measurable
  rw [integral_Ici_eq_integral_Ioi, integral_eq_lintegral_of_nonneg_ae]
  · rw [← ltsurv_mean_integral_eq μ X hX hXnn s hs, integral_eq_lintegral_of_nonneg_ae]
    · rw [layer]
      congr 1
      refine setLIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
      rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_toReal (measure_ne_top _ _),
        mul_comm]
    · refine Eventually.of_forall fun ω => ?_
      have h1 : Real.exp (-(s * X ω)) ≤ 1 := by
        rw [Real.exp_le_one_iff]; have := hXnn ω; nlinarith
      exact div_nonneg (by linarith) hs.le
    · exact (by fun_prop : Measurable fun ω => (1 - Real.exp (-(s * X ω))) / s).aestronglyMeasurable
  · exact Eventually.of_forall fun x => mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg
  · exact ((by fun_prop : Measurable fun x : ℝ => Real.exp (-(s * x))).mul hmeas).aestronglyMeasurable

open MeasureTheory StochasticOrders.LaplaceTransform in
theorem solution {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (X : Ω → ℝ) (Y : Ω' → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXnn : ∀ ω, 0 ≤ X ω) (hYnn : ∀ ω, 0 ≤ Y ω) :
    LaplaceOrder μ ν X Y ↔
      ∀ s : ℝ, 0 < s →
        ∫ x in Set.Ici (0 : ℝ), Real.exp (-(s * x)) * (μ {ω | x < X ω}).toReal ≤
          ∫ x in Set.Ici (0 : ℝ), Real.exp (-(s * x)) * (ν {ω | x < Y ω}).toReal := by
  constructor
  · intro h s hs
    rw [ltsurv_identity μ X hX hXnn s hs, ltsurv_identity ν Y hY hYnn s hs]
    have := h s hs
    exact div_le_div_of_nonneg_right (by linarith) hs.le
  · intro h s hs
    have := h s hs
    rw [ltsurv_identity μ X hX hXnn s hs, ltsurv_identity ν Y hY hYnn s hs,
      div_le_div_iff_of_pos_right hs] at this
    show ∫ ω, Real.exp (-(s * X ω)) ∂μ ≥ ∫ ω, Real.exp (-(s * Y ω)) ∂ν
    linarith

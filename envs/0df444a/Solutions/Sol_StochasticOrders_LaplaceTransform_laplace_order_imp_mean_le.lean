-- Prove2me | solution 1 for StochasticOrders.LaplaceTransform.laplace_order_imp_mean_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T09:19:20.709034+00:00
-- url     : https://prove2.me/submissions/db342aaa-14f7-4276-bc48-d538a77aba4a

import Mathlib
import Definitions.Def_StochasticOrders_LaplaceTransform_LaplaceOrder

set_option autoImplicit false

open MeasureTheory Filter Topology

/-- `(1 - e^{-s x}) / s → x` as `s → 0⁺`. -/
theorem ltmean_slope_tendsto (x : ℝ) :
    Tendsto (fun s : ℝ => (1 - Real.exp (-(s * x))) / s) (𝓝[>] 0) (𝓝 x) := by
  have h : HasDerivAt (fun s : ℝ => -Real.exp (-(s * x))) x 0 := by
    have h1 : HasDerivAt (fun s : ℝ => -(s * x)) (-x) 0 := by
      exact (hasDerivAt_mul_const (x := (0:ℝ)) x).fun_neg
    have h2 : HasDerivAt (fun s : ℝ => Real.exp (-(s * x))) (Real.exp (-(0 * x)) * -x) 0 :=
      h1.exp
    have h3 := h2.fun_neg
    simp only [zero_mul, neg_zero, Real.exp_zero, one_mul, neg_neg] at h3
    exact h3
  have := h.tendsto_slope_zero_right
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp only [zero_add, zero_mul, neg_zero, Real.exp_zero, smul_eq_mul]
  rw [div_eq_inv_mul]
  ring

theorem ltmean_bound (s x : ℝ) (hs : 0 < s) (hx : 0 ≤ x) :
    ‖(1 - Real.exp (-(s * x))) / s‖ ≤ x := by
  have h1 : Real.exp (-(s * x)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith
  have h2 : 1 - s * x ≤ Real.exp (-(s * x)) := by
    have := Real.add_one_le_exp (-(s * x)); linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by linarith) hs.le), div_le_iff₀ hs]
  linarith

theorem ltmean_integral_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X) (hXnn : ∀ ω, 0 ≤ X ω)
    (s : ℝ) (hs : 0 < s) :
    ∫ ω, (1 - Real.exp (-(s * X ω))) / s ∂μ = (1 - ∫ ω, Real.exp (-(s * X ω)) ∂μ) / s := by
  have hint : Integrable (fun ω => Real.exp (-(s * X ω))) μ := by
    refine Integrable.of_bound (C := 1) (by fun_prop) (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    have := hXnn ω; nlinarith
  rw [integral_div, integral_sub (integrable_const _) hint, integral_const]
  simp

theorem ltmean_tendsto {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X) (hXnn : ∀ ω, 0 ≤ X ω)
    (hXint : Integrable X μ) :
    Tendsto (fun s : ℝ => (1 - ∫ ω, Real.exp (-(s * X ω)) ∂μ) / s) (𝓝[>] 0)
      (𝓝 (∫ ω, X ω ∂μ)) := by
  have key : Tendsto (fun s : ℝ => ∫ ω, (1 - Real.exp (-(s * X ω))) / s ∂μ) (𝓝[>] 0)
      (𝓝 (∫ ω, X ω ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence X ?_ ?_ hXint ?_
    · exact Eventually.of_forall fun s => by fun_prop
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact Eventually.of_forall fun ω => ltmean_bound s (X ω) hs (hXnn ω)
    · exact Eventually.of_forall fun ω => ltmean_slope_tendsto (X ω)
  refine key.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact ltmean_integral_eq μ X hX hXnn s hs

open MeasureTheory StochasticOrders.LaplaceTransform in
theorem solution {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → ℝ) (Y : Ω' → ℝ) (hX : Measurable X) (hY : Measurable Y) (hXnn : ∀ ω, 0 ≤ X ω)
    (hYnn : ∀ ω, 0 ≤ Y ω) (hXint : Integrable X μ) (hYint : Integrable Y ν)
    (h : LaplaceOrder μ ν X Y) :
    ∫ ω, X ω ∂μ ≤ ∫ ω, Y ω ∂ν := by
  refine le_of_tendsto_of_tendsto (ltmean_tendsto μ X hX hXnn hXint)
    (ltmean_tendsto ν Y hY hYnn hYint) ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have := h s hs
  exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hs)

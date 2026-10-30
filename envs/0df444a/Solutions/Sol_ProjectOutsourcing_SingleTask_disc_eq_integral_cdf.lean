-- Prove2me | solution 1 for ProjectOutsourcing.SingleTask.disc_eq_integral_cdf
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T22:56:12.558554+00:00
-- url     : https://prove2.me/submissions/60f2b67d-d997-4807-90ec-06067a46dcf5

import Mathlib
import Definitions.Def_ProjectOutsourcing_SingleTask_Setting

open ProjectOutsourcing.SingleTask MeasureTheory Set

theorem solution (M : Model) (hM : M.Valid) (s r : ℝ) (hs : 0 < s) (hr : 0 < r) :
    disc M s r = s * ∫ t in Set.Ioi 0, Real.exp (-(s * t)) * M.F (r * t) := by
  have := hM.isProb
  -- the kernel
  set f : ℝ → ℝ → ℝ := fun z t => (Ioi (z / r)).indicator (fun t => s * Real.exp (-(s * t))) t
    with hf
  -- z-side: f z t = (Iio (r t)).indicator const
  have hzt : ∀ z t, f z t = (Iio (r * t)).indicator (fun _ => s * Real.exp (-(s * t))) z := by
    intro z t
    simp only [hf, Set.indicator, Set.mem_Ioi, Set.mem_Iio]
    have : z / r < t ↔ z < r * t := by
      rw [div_lt_iff₀ hr, mul_comm]
    simp [this]
  -- singletons are null
  have hsing : ∀ a : ℝ, M.μ {a} = 0 := fun a => hM.hasPdf (Real.volume_singleton)
  have hinner_z : ∀ t, ∫ z, f z t ∂M.μ = s * Real.exp (-(s * t)) * M.F (r * t) := by
    intro t
    simp_rw [hzt]
    rw [integral_indicator_const _ measurableSet_Iio, smul_eq_mul, mul_comm]
    congr 1
    unfold Model.F
    rw [Measure.real, measure_congr (Iio_ae_eq_Iic' (hsing (r * t)))]
  -- t-side for z ≥ 0
  have hinner_t : ∀ z, 0 ≤ z → ∫ t in Ioi 0, f z t = Real.exp (-(s * z / r)) := by
    intro z hz
    simp only [hf]
    rw [setIntegral_indicator measurableSet_Ioi, Set.Ioi_inter_Ioi,
      sup_eq_right.mpr (div_nonneg hz hr.le)]
    rw [integral_const_mul]
    have := integral_exp_mul_Ioi (a := -s) (by linarith) (z / r)
    simp only [neg_mul] at this ⊢
    rw [this]
    field_simp
  -- a.e. nonnegativity
  have hae : ∀ᵐ z ∂M.μ, 0 ≤ z := by
    rw [ae_iff]
    have : {a : ℝ | ¬ 0 ≤ a} = Iio 0 := by ext; simp
    rw [this]; exact hM.nonneg
  -- integrability on the product
  have hmeas : Measurable (Function.uncurry f) := by
    have : Function.uncurry f = fun p : ℝ × ℝ =>
        if p.1 / r < p.2 then s * Real.exp (-(s * p.2)) else 0 := by
      ext p; simp only [hf, Set.indicator, Function.uncurry, Set.mem_Ioi]
    rw [this]
    refine Measurable.ite ?_ (by fun_prop) measurable_const
    exact measurableSet_lt (by fun_prop) (by fun_prop)
  have hint : Integrable (Function.uncurry f) (M.μ.prod (volume.restrict (Ioi (0:ℝ)))) := by
    have hg : Integrable (fun t : ℝ => s * Real.exp (-(s * t))) (volume.restrict (Ioi (0:ℝ))) := by
      have := (exp_neg_integrableOn_Ioi 0 hs).const_mul s
      simpa [neg_mul] using this
    have hb := (integrable_const (1:ℝ) (μ := M.μ)).mul_prod hg
    refine hb.mono' hmeas.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun p => ?_)
    simp only [Function.uncurry, hf, one_mul, Set.indicator]
    split_ifs
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    · simp; positivity
  unfold disc
  rw [if_pos hr]
  calc ∫ z, Real.exp (-(s * z / r)) ∂M.μ = ∫ z, (∫ t in Ioi 0, f z t) ∂M.μ := by
        refine integral_congr_ae ?_
        filter_upwards [hae] with z hz
        exact (hinner_t z hz).symm
    _ = ∫ t in Ioi 0, ∫ z, f z t ∂M.μ := integral_integral_swap hint
    _ = ∫ t in Ioi 0, s * (Real.exp (-(s * t)) * M.F (r * t)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        simp only [hinner_z, mul_assoc]
    _ = s * ∫ t in Set.Ioi 0, Real.exp (-(s * t)) * M.F (r * t) := integral_const_mul _ _

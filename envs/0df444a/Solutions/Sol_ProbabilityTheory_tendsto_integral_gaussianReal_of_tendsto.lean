-- Prove2me | solution 1 for ProbabilityTheory.tendsto_integral_gaussianReal_of_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-16T01:12:49.132753+00:00
-- url     : https://prove2.me/submissions/e5964b0f-a24d-44ed-bdcd-b07f9ec2e1ec

import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Portmanteau

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

set_option maxHeartbeats 2000000

theorem solution (u : ℕ → ℝ≥0) (c : ℝ≥0)
    (hu : Tendsto (fun K => (u K : ℝ)) atTop (𝓝 (c : ℝ)))
    (f : ℝ → ℝ) (L : ℝ≥0) (hL : LipschitzWith L f) (C : ℝ) (hC : ∀ x y, dist (f x) (f y) ≤ C) :
    Tendsto (fun K => ∫ x, f x ∂(gaussianReal 0 (u K))) atTop
      (𝓝 (∫ x, f x ∂(gaussianReal 0 c))) := by
  classical
  -- `N(0,t)` is the pushforward of `N(0,1)` under multiplication by `√t`
  have hmap : ∀ t : ℝ≥0, (gaussianReal 0 1).map (fun y => Real.sqrt t * y) = gaussianReal 0 t := by
    intro t
    have h := gaussianReal_map_const_mul (μ := 0) (v := 1) (Real.sqrt t)
    have ht : NNReal.mk (Real.sqrt t ^ 2) (sq_nonneg _) * 1 = t := by
      rw [mul_one]
      refine NNReal.eq ?_
      rw [NNReal.coe_mk]
      exact Real.sq_sqrt t.coe_nonneg
    rw [mul_zero, ht] at h
    exact h
  -- `f` is bounded
  have hfb : ∀ x, |f x| ≤ |f 0| + C := by
    intro x
    have := hC x 0
    rw [Real.dist_eq] at this
    have h2 : |f x| - |f 0| ≤ |f x - f 0| := abs_sub_abs_le_abs_sub _ _
    linarith
  have hfcont : Continuous f := hL.continuous
  -- integrability of `y ↦ f (a * y)` against the standard Gaussian
  have hint : ∀ a : ℝ, Integrable (fun y => f (a * y)) (gaussianReal 0 1) := by
    intro a
    exact ⟨(hfcont.comp (continuous_const.mul continuous_id)).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (C := |f 0| + C)
        (ae_of_all _ (fun y => by simpa using hfb (a * y)))⟩
  -- the first absolute moment of the standard Gaussian
  have habs : Integrable (fun y : ℝ => |y|) (gaussianReal 0 1) := by
    have h1 : MemLp (id : ℝ → ℝ) 1 (gaussianReal 0 1) := memLp_id_gaussianReal' 1 (by simp)
    exact (memLp_one_iff_integrable.mp h1).abs
  set M : ℝ := ∫ y, |y| ∂(gaussianReal 0 1) with hM
  have hM0 : 0 ≤ M := integral_nonneg (fun y => abs_nonneg _)
  -- rewrite every Gaussian integral as an integral against `N(0,1)`
  have hrw : ∀ t : ℝ≥0, ∫ x, f x ∂(gaussianReal 0 t)
      = ∫ y, f (Real.sqrt t * y) ∂(gaussianReal 0 1) := by
    intro t
    rw [← hmap t, integral_map (by fun_prop) hfcont.aestronglyMeasurable]
  simp only [hrw]
  -- the elementary bound
  have hbd : ∀ t : ℝ≥0, |(∫ y, f (Real.sqrt t * y) ∂(gaussianReal 0 1))
        - ∫ y, f (Real.sqrt c * y) ∂(gaussianReal 0 1)|
      ≤ (L : ℝ) * |Real.sqrt t - Real.sqrt c| * M := by
    intro t
    have hsub : (∫ y, f (Real.sqrt t * y) ∂(gaussianReal 0 1))
        - ∫ y, f (Real.sqrt c * y) ∂(gaussianReal 0 1)
        = ∫ y, (f (Real.sqrt t * y) - f (Real.sqrt c * y)) ∂(gaussianReal 0 1) :=
      (integral_sub (hint _) (hint _)).symm
    rw [hsub]
    have hptw : ∀ y : ℝ, |f (Real.sqrt t * y) - f (Real.sqrt c * y)|
        ≤ (L : ℝ) * |Real.sqrt t - Real.sqrt c| * |y| := by
      intro y
      have h := hL.dist_le_mul (Real.sqrt t * y) (Real.sqrt c * y)
      rw [Real.dist_eq, Real.dist_eq] at h
      calc |f (Real.sqrt t * y) - f (Real.sqrt c * y)|
          ≤ (L : ℝ) * |Real.sqrt t * y - Real.sqrt c * y| := h
        _ = (L : ℝ) * (|Real.sqrt t - Real.sqrt c| * |y|) := by
              rw [← abs_mul, sub_mul]
        _ = (L : ℝ) * |Real.sqrt t - Real.sqrt c| * |y| := by ring
    have h1 : |∫ y, (f (Real.sqrt t * y) - f (Real.sqrt c * y)) ∂(gaussianReal 0 1)|
        ≤ ∫ y, |f (Real.sqrt t * y) - f (Real.sqrt c * y)| ∂(gaussianReal 0 1) :=
      abs_integral_le_integral_abs
    have h2 : ∫ y, |f (Real.sqrt t * y) - f (Real.sqrt c * y)| ∂(gaussianReal 0 1)
        ≤ ∫ y, (L : ℝ) * |Real.sqrt t - Real.sqrt c| * |y| ∂(gaussianReal 0 1) :=
      integral_mono ((hint _).sub (hint _)).abs (habs.const_mul _) hptw
    have h3 : ∫ y, (L : ℝ) * |Real.sqrt t - Real.sqrt c| * |y| ∂(gaussianReal 0 1)
        = (L : ℝ) * |Real.sqrt t - Real.sqrt c| * M := by
      rw [integral_const_mul]
    linarith
  -- squeeze
  have hsq : Tendsto (fun K => Real.sqrt (u K)) atTop (𝓝 (Real.sqrt c)) :=
    (Real.continuous_sqrt.tendsto _).comp hu
  have hgo : Tendsto (fun K => (L : ℝ) * |Real.sqrt (u K) - Real.sqrt c| * M) atTop (𝓝 0) := by
    have hd : Tendsto (fun K => Real.sqrt (u K) - Real.sqrt c) atTop (𝓝 0) :=
      tendsto_sub_nhds_zero_iff.mpr hsq
    have habs0 : Tendsto (fun K => |Real.sqrt (u K) - Real.sqrt c|) atTop (𝓝 0) := by
      simpa using hd.abs
    have h2 := (habs0.const_mul (L : ℝ)).mul_const M
    simpa using h2
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm (fun K => ?_) hgo
  simpa [Real.norm_eq_abs] using hbd (u K)

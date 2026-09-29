-- Prove2me | solution 1 for ProbabilityTheory.integral_cos_gaussianReal
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-16T01:07:57.765107+00:00
-- url     : https://prove2.me/submissions/33bb1009-053e-481f-9b32-8be5d82694d8

import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

set_option maxHeartbeats 2000000

theorem solution (v : ℝ≥0) :
    ∫ x, Real.cos x ∂(gaussianReal 0 v) = Real.exp (-(v : ℝ) / 2) := by
  have hcont : Continuous (fun x : ℝ => Complex.exp (1 * (x : ℂ) * Complex.I)) := by
    fun_prop
  have hnorm : ∀ x : ℝ, ‖Complex.exp (1 * (x : ℂ) * Complex.I)‖ = 1 := by
    intro x
    rw [Complex.norm_exp]
    simp
  have hI : Integrable (fun x : ℝ => Complex.exp (1 * (x : ℂ) * Complex.I))
      (gaussianReal 0 v) :=
    ⟨hcont.aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (C := 1) (ae_of_all _ (fun x => (hnorm x).le))⟩
  have h1 : ∫ x : ℝ, Complex.exp (1 * (x : ℂ) * Complex.I) ∂(gaussianReal 0 v)
      = Complex.exp (-((v : ℝ) : ℂ) / 2) := by
    have := charFun_gaussianReal (μ := 0) (v := v) 1
    rw [charFun_apply_real] at this
    push_cast at this ⊢
    rw [this]
    norm_num
    ring_nf
  have hre := integral_re (𝕜 := ℂ) hI
  rw [h1] at hre
  have hlhs : ∀ x : ℝ, RCLike.re (Complex.exp (1 * (x : ℂ) * Complex.I)) = Real.cos x := by
    intro x
    rw [one_mul, Complex.exp_mul_I]
    simp [Complex.cos_ofReal_re]
  have hrhs : RCLike.re (Complex.exp (-((v : ℝ) : ℂ) / 2)) = Real.exp (-(v : ℝ) / 2) := by
    have : (-((v : ℝ) : ℂ) / 2) = ((-(v : ℝ) / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this]
    exact Complex.exp_ofReal_re _
  rw [hrhs] at hre
  simp only [hlhs] at hre
  exact hre

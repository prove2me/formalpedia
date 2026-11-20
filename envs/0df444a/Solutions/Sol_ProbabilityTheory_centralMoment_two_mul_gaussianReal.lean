-- Prove2me | solution 1 for ProbabilityTheory.centralMoment_two_mul_gaussianReal
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T07:44:20.616995+00:00
-- url     : https://prove2.me/submissions/01822bad-466d-4569-a9b3-4f99c7ff118a

import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral


@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

open Real in
theorem _root_.solution (μ : ℝ) (σ : ℝ≥0) (n : ℕ) :
    centralMoment id (2 * n) (gaussianReal μ (σ^2))
    = σ ^ (2 * n) * Nat.doubleFactorial (2 * n - 1) := by
  show ∫ x, (x - ∫ y, y ∂(gaussianReal μ (σ^2))) ^ (2 * n) ∂(gaussianReal μ (σ^2)) = _
  rcases eq_or_ne σ 0 with h0 | h0
  · subst h0
    rcases n with _ | n
    · simp
    · simp [gaussianReal_zero_var]
  have hv : σ ^ 2 ≠ 0 := pow_ne_zero 2 h0
  rw [integral_id_gaussianReal, integral_gaussianReal_eq_integral_smul hv]
  simp only [gaussianPDFReal, smul_eq_mul]
  set v : ℝ := ((σ ^ 2 : ℝ≥0) : ℝ) with hvdef
  have hvpos : 0 < v := by rw [hvdef]; positivity
  have hs : (σ : ℝ) ^ 2 = v := by rw [hvdef]; push_cast; ring
  set b : ℝ := 1 / (2 * v) with hb
  have hbpos : 0 < b := by positivity
  have h1 := integral_sub_right_eq_self (μ := volume)
    (fun x : ℝ => (√(2 * π * v))⁻¹ * rexp (-x ^ 2 / (2 * v)) * x ^ (2 * n)) μ
  rw [h1]
  have e : (fun x : ℝ => (√(2 * π * v))⁻¹ * rexp (-x ^ 2 / (2 * v)) * x ^ (2 * n))
      = fun x => (√(2 * π * v))⁻¹ *
        ((fun y : ℝ => y ^ ((2 * n : ℕ) : ℝ) * rexp (-b * y ^ (2 : ℝ))) |x|) := by
    funext x
    beta_reduce
    rw [Real.rpow_natCast, Real.rpow_two, sq_abs, (even_two_mul n).pow_abs, hb]
    ring_nf
  rw [e, integral_const_mul, integral_comp_abs (f := fun y : ℝ => y ^ ((2 * n : ℕ) : ℝ) * rexp (-b * y ^ (2 : ℝ))),
    integral_rpow_mul_exp_neg_mul_rpow two_pos (by linarith [show (0:ℝ) ≤ ((2 * n : ℕ) : ℝ) from Nat.cast_nonneg _]) hbpos]
  have hg : (((2 * n : ℕ) : ℝ) + 1) / 2 = (n : ℝ) + 1 / 2 := by push_cast; ring
  rw [hg, Real.Gamma_nat_add_half]
  have hb2 : b ^ (-((n : ℝ) + 1 / 2)) = (2 * v) ^ n * √(2 * v) := by
    rw [hb, one_div, Real.inv_rpow (by positivity), Real.rpow_neg (by positivity), inv_inv,
      Real.rpow_add (by positivity), Real.rpow_natCast, Real.sqrt_eq_rpow]
  have hneg : -(((2 * n : ℕ) : ℝ) + 1) / 2 = -((n : ℝ) + 1 / 2) := by push_cast; ring
  rw [hneg, hb2]
  have hsq : √(2 * π * v) = √(2 * v) * √π := by
    rw [show 2 * π * v = (2 * v) * π by ring, Real.sqrt_mul (by positivity)]
  rw [hsq]
  have hsv : 0 < √(2 * v) := Real.sqrt_pos.2 (by positivity)
  have hspi : 0 < √π := Real.sqrt_pos.2 Real.pi_pos
  rw [pow_mul, hs, mul_pow]
  field_simp

end ProbabilityTheory

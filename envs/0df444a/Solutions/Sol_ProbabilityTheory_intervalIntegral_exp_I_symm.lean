-- Prove2me | solution 1 for ProbabilityTheory.intervalIntegral_exp_I_symm
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T00:11:31.992199+00:00
-- url     : https://prove2.me/submissions/ee1cb291-9543-42fe-9076-d504d9d4b719

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.PosLog

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

/-- The symmetric Fourier average of an imaginary exponential is sinc. -/
theorem solution :
    ∀ (x : ℝ), (1 / 2 : ℂ) * ∫ u in (-1 : ℝ)..1,
      Complex.exp (↑u * ↑x * I) = (Real.sinc x : ℂ) := by
  intro x
  by_cases hx : x = 0
  · subst hx
    have hconst : (fun u : ℝ => Complex.exp (↑u * ↑(0 : ℝ) * I)) = fun _ => (1 : ℂ) := by
      funext u; simp
    have hint : (∫ u in (-1 : ℝ)..1, Complex.exp (↑u * ↑(0 : ℝ) * I)) = 2 := by
      rw [hconst, intervalIntegral.integral_const]
      show ((1 : ℝ) - (-1 : ℝ)) • (1 : ℂ) = 2
      rw [RCLike.real_smul_eq_coe_mul (K := ℂ)]
      push_cast
      norm_num
    rw [hint, Real.sinc_zero, Complex.ofReal_one]
    norm_num
  · have hxC : (↑x : ℂ) ≠ 0 := by exact_mod_cast hx
    have hc : (↑x * I : ℂ) ≠ 0 := mul_ne_zero hxC Complex.I_ne_zero
    have hrw : (∫ u in (-1 : ℝ)..1, Complex.exp (↑u * ↑x * I))
        = ∫ u in (-1 : ℝ)..1, Complex.exp ((↑x * I) * ↑u) := by
      refine intervalIntegral.integral_congr (fun u _ => ?_)
      congr 1
      ring
    rw [hrw, integral_exp_mul_complex hc, Real.sinc_of_ne_zero hx, Complex.ofReal_div,
        Complex.ofReal_sin]
    have key : Complex.exp (↑x * I * ↑(1 : ℝ)) - Complex.exp (↑x * I * ↑(-1 : ℝ))
        = 2 * (Complex.sin ↑x * I) := by
      rw [Complex.ofReal_one, Complex.ofReal_neg, Complex.ofReal_one, mul_one, mul_neg_one,
          show -(↑x * I) = ((-↑x : ℂ)) * I from by ring, Complex.exp_mul_I, Complex.exp_mul_I,
          Complex.cos_neg, Complex.sin_neg]
      ring
    rw [key]
    field_simp

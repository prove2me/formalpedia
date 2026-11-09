-- Prove2me | solution 1 for ProbabilityTheory.leanlevy_chat23_intInt_exp_shift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T12:51:24.193604+00:00
-- url     : https://prove2.me/submissions/90df8f18-8eda-4186-aea1-1dd223081131

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

/-- The source Fourier average, expanded locally to avoid fragile imported source modules. -/
theorem solution (ξ x : ℝ) :
    ∫ u in (-1 : ℝ)..1, Complex.exp (↑x * ↑(ξ + u) * Complex.I)
      = Complex.exp (↑x * ↑ξ * Complex.I) * (2 * (Real.sinc x : ℂ)) := by
  have hSymm (y : ℝ) :
      (1 / 2 : ℂ) * ∫ u in (-1 : ℝ)..1, Complex.exp (↑u * ↑y * Complex.I)
        = (Real.sinc y : ℂ) := by
    by_cases hy : y = 0
    · subst hy
      have hconst : (fun u : ℝ => Complex.exp (↑u * ↑(0 : ℝ) * Complex.I))
          = fun _ => (1 : ℂ) := by
        funext u; simp
      have hint : (∫ u in (-1 : ℝ)..1,
          Complex.exp (↑u * ↑(0 : ℝ) * Complex.I)) = 2 := by
        rw [hconst, intervalIntegral.integral_const]
        show ((1 : ℝ) - (-1 : ℝ)) • (1 : ℂ) = 2
        rw [RCLike.real_smul_eq_coe_mul (K := ℂ)]
        push_cast
        norm_num
      rw [hint, Real.sinc_zero, Complex.ofReal_one]
      norm_num
    · have hyC : (↑y : ℂ) ≠ 0 := by exact_mod_cast hy
      have hc : (↑y * Complex.I : ℂ) ≠ 0 :=
        mul_ne_zero hyC Complex.I_ne_zero
      have hrw : (∫ u in (-1 : ℝ)..1,
          Complex.exp (↑u * ↑y * Complex.I))
          = ∫ u in (-1 : ℝ)..1, Complex.exp ((↑y * Complex.I) * ↑u) := by
        refine intervalIntegral.integral_congr (fun u _ => ?_)
        congr 1
        ring
      rw [hrw, integral_exp_mul_complex hc, Real.sinc_of_ne_zero hy,
        Complex.ofReal_div, Complex.ofReal_sin]
      have key : Complex.exp (↑y * Complex.I * ↑(1 : ℝ)) -
          Complex.exp (↑y * Complex.I * ↑(-1 : ℝ))
          = 2 * (Complex.sin ↑y * Complex.I) := by
        rw [Complex.ofReal_one, Complex.ofReal_neg, Complex.ofReal_one,
          mul_one, mul_neg_one,
          show -(↑y * Complex.I) = ((-↑y : ℂ)) * Complex.I from by ring,
          Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
        ring
      rw [key]
      field_simp
  have hcongr : (fun u : ℝ => Complex.exp (↑x * ↑(ξ + u) * Complex.I))
      = fun u : ℝ => Complex.exp (↑x * ↑ξ * Complex.I) *
          Complex.exp (↑u * ↑x * Complex.I) := by
    funext u
    rw [← Complex.exp_add]
    congr 1
    push_cast; ring
  rw [hcongr, show (∫ u in (-1 : ℝ)..1,
        Complex.exp (↑x * ↑ξ * Complex.I) * Complex.exp (↑u * ↑x * Complex.I))
      = Complex.exp (↑x * ↑ξ * Complex.I) * ∫ u in (-1 : ℝ)..1,
          Complex.exp (↑u * ↑x * Complex.I)
    from intervalIntegral.integral_const_mul _ _]
  congr 1
  rw [← hSymm x]
  ring

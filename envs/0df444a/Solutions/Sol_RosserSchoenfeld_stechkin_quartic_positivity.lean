-- Prove2me | solution 1 for RosserSchoenfeld.stechkin_quartic_positivity
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-10-03T17:35:56.757607+00:00
-- url     : https://prove2.me/submissions/781de069-7fd6-432d-acb3-f1df15163635

import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

set_option autoImplicit false

open Finset Complex ArithmeticFunction
open scoped LSeries.notation

namespace RosserSchoenfeld

/-- The exact rational coefficients of the quartic used on page 250 of Rosser--Schoenfeld (1975). -/
def coefficient : Fin 5 → ℝ :=
  ![11.1859355312082048, 19.073344004352, 11.67618784, 4.7568, 1]

lemma coefficient_pos (k : Fin 5) : 0 < coefficient k := by
  fin_cases k <;> norm_num [coefficient]

lemma cosine_polynomial_factorization (t : ℝ) :
    (∑ k : Fin 5, coefficient k * Real.cos ((k : ℝ) * t)) =
      8 * (0.9126 + Real.cos t) ^ 2 * (0.2766 + Real.cos t) ^ 2 := by
  have hfour : Real.cos (4 * t) = 2 * (2 * Real.cos t ^ 2 - 1) ^ 2 - 1 := by
    rw [show (4 : ℝ) * t = 2 * (2 * t) by ring, Real.cos_two_mul,
      Real.cos_two_mul]
  norm_num [Fin.sum_univ_succ, coefficient, Real.cos_two_mul, Real.cos_three_mul, hfour]
  ring

lemma cosine_polynomial_nonneg (t : ℝ) :
    0 ≤ ∑ k : Fin 5, coefficient k * Real.cos ((k : ℝ) * t) := by
  rw [cosine_polynomial_factorization]
  positivity

lemma real_vonMangoldt_term (sigma t : ℝ) (n : ℕ) :
    (LSeries.term (fun m => (vonMangoldt m : ℂ)) (sigma + t * I) n).re =
      vonMangoldt n * Real.exp (-Real.log n * sigma) * Real.cos (t * Real.log n) := by
  by_cases hn : n = 0
  · simp [hn]
  rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← cpow_neg,
    cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn), ← natCast_log]
  simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, exp_re,
    mul_im, add_re, add_im, neg_re, neg_im, I_re, I_im, mul_zero, mul_one,
    zero_add, add_zero]
  simp only [mul_neg, Real.cos_neg]
  ring

/-- A nonnegative cosine polynomial gives a nonnegative linear combination of
negative logarithmic derivatives of zeta throughout the absolute-convergence half-plane. -/
lemma nonnegative_logDeriv_combination {N : ℕ} (a : Fin N → ℝ)
    (ha : ∀ u : ℝ, 0 ≤ ∑ k : Fin N, a k * Real.cos ((k : ℝ) * u))
    (sigma t : ℝ) (hsigma : 1 < sigma) :
    0 ≤ ∑ k : Fin N, a k *
      (-deriv riemannZeta (sigma + (k : ℝ) * t * I) /
        riemannZeta (sigma + (k : ℝ) * t * I)).re := by
  have hre (k : Fin N) : 1 < (sigma + (k : ℝ) * t * I : ℂ).re := by
    simpa using hsigma
  have hsum (k : Fin N) : Summable fun n =>
      (LSeries.term (fun m => (vonMangoldt m : ℂ)) (sigma + (k : ℝ) * t * I) n).re :=
    (hasSum_re (LSeriesSummable_vonMangoldt (hre k)).hasSum).summable
  have hrepr (k : Fin N) :
      (-deriv riemannZeta (sigma + (k : ℝ) * t * I) /
        riemannZeta (sigma + (k : ℝ) * t * I)).re =
      ∑' n, (LSeries.term (fun m => (vonMangoldt m : ℂ))
        (sigma + (k : ℝ) * t * I) n).re := by
    rw [← LSeries_vonMangoldt_eq_deriv_riemannZeta_div (hre k), LSeries,
      re_tsum (LSeriesSummable_vonMangoldt (hre k))]
  simp_rw [hrepr, ← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun k _ => (hsum k).mul_left (a k))]
  apply tsum_nonneg
  intro n
  simp_rw [← Complex.ofReal_mul, real_vonMangoldt_term]
  have hfact : (∑ k : Fin N, a k *
      (vonMangoldt n * Real.exp (-Real.log n * sigma) *
        Real.cos (((k : ℝ) * t) * Real.log n))) =
      (vonMangoldt n * Real.exp (-Real.log n * sigma)) *
        ∑ k : Fin N, a k * Real.cos ((k : ℝ) * (t * Real.log n)) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro k _
    rw [mul_assoc (k : ℝ) t]
    ring
  rw [hfact]
  exact mul_nonneg (mul_nonneg vonMangoldt_nonneg (Real.exp_pos _).le) (ha _)

/-- The quartic positivity input used to derive the explicit zero-free region. -/
lemma rosser_schoenfeld_logDeriv_nonneg (sigma t : ℝ) (hsigma : 1 < sigma) :
    0 ≤ ∑ k : Fin 5, coefficient k *
      (-deriv riemannZeta (sigma + (k : ℝ) * t * I) /
        riemannZeta (sigma + (k : ℝ) * t * I)).re :=
  nonnegative_logDeriv_combination coefficient cosine_polynomial_nonneg sigma t hsigma

/-- The positivity input remains valid after subtracting a shifted Dirichlet series,
which is the Stechkin modification in equation (1.10) of the source. -/
lemma nonnegative_modified_logDeriv_combination {N : ℕ} (a : Fin N → ℝ)
    (ha : ∀ u : ℝ, 0 ≤ ∑ k : Fin N, a k * Real.cos ((k : ℝ) * u))
    (sigma sigma0 kappa t : ℝ) (hsigma : 1 < sigma)
    (hshift : sigma ≤ sigma0) (hkappa : kappa ≤ 1) :
    0 ≤ ∑ k : Fin N, a k *
      ((-deriv riemannZeta (sigma + (k : ℝ) * t * I) /
          riemannZeta (sigma + (k : ℝ) * t * I)).re -
        kappa * (-deriv riemannZeta (sigma0 + (k : ℝ) * t * I) /
          riemannZeta (sigma0 + (k : ℝ) * t * I)).re) := by
  have hre (s : ℝ) (hs : 1 < s) (k : Fin N) :
      1 < (s + (k : ℝ) * t * I : ℂ).re := by simpa using hs
  have hsum (s : ℝ) (hs : 1 < s) (k : Fin N) : Summable fun n =>
      (LSeries.term (fun m => (vonMangoldt m : ℂ)) (s + (k : ℝ) * t * I) n).re :=
    (hasSum_re (LSeriesSummable_vonMangoldt (hre s hs k)).hasSum).summable
  have hrepr (s : ℝ) (hs : 1 < s) (k : Fin N) :
      (-deriv riemannZeta (s + (k : ℝ) * t * I) /
        riemannZeta (s + (k : ℝ) * t * I)).re =
      ∑' n, (LSeries.term (fun m => (vonMangoldt m : ℂ))
        (s + (k : ℝ) * t * I) n).re := by
    rw [← LSeries_vonMangoldt_eq_deriv_riemannZeta_div (hre s hs k), LSeries,
      re_tsum (LSeriesSummable_vonMangoldt (hre s hs k))]
  have hsigma0 : 1 < sigma0 := hsigma.trans_le hshift
  simp_rw [hrepr sigma hsigma, hrepr sigma0 hsigma0, ← tsum_mul_left]
  simp_rw [← Summable.tsum_sub (hsum sigma hsigma _) ((hsum sigma0 hsigma0 _).mul_left kappa),
    ← tsum_mul_left]
  rw [← Summable.tsum_finsetSum
    (fun k _ => ((hsum sigma hsigma k).sub ((hsum sigma0 hsigma0 k).mul_left kappa)).mul_left (a k))]
  apply tsum_nonneg
  intro n
  simp_rw [← Complex.ofReal_mul, real_vonMangoldt_term]
  have hweight : 0 ≤ Real.exp (-Real.log n * sigma) -
      kappa * Real.exp (-Real.log n * sigma0) := by
    have hexp : Real.exp (-Real.log n * sigma0) ≤ Real.exp (-Real.log n * sigma) := by
      apply Real.exp_le_exp.mpr
      nlinarith [Real.log_natCast_nonneg n]
    have := mul_le_of_le_one_left (Real.exp_pos (-Real.log n * sigma0)).le hkappa
    linarith
  have hfact : (∑ k : Fin N, a k *
      (vonMangoldt n * Real.exp (-Real.log n * sigma) *
          Real.cos (((k : ℝ) * t) * Real.log n) -
        kappa * (vonMangoldt n * Real.exp (-Real.log n * sigma0) *
          Real.cos (((k : ℝ) * t) * Real.log n)))) =
      (vonMangoldt n * (Real.exp (-Real.log n * sigma) -
          kappa * Real.exp (-Real.log n * sigma0))) *
        ∑ k : Fin N, a k * Real.cos ((k : ℝ) * (t * Real.log n)) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro k _
    rw [mul_assoc (k : ℝ) t]
    ring
  rw [hfact]
  exact mul_nonneg (mul_nonneg vonMangoldt_nonneg hweight) (ha _)

/-- Rosser--Schoenfeld's nonnegative quartic combined with the Stechkin modification. -/
lemma rosser_schoenfeld_modified_logDeriv_nonneg
    (sigma sigma0 kappa t : ℝ) (hsigma : 1 < sigma)
    (hshift : sigma ≤ sigma0) (hkappa : kappa ≤ 1) :
    0 ≤ ∑ k : Fin 5, coefficient k *
      ((kappa : ℂ) * deriv riemannZeta (sigma0 + (k : ℝ) * t * I) /
          riemannZeta (sigma0 + (k : ℝ) * t * I) -
        deriv riemannZeta (sigma + (k : ℝ) * t * I) /
          riemannZeta (sigma + (k : ℝ) * t * I)).re := by
  have h := nonnegative_modified_logDeriv_combination coefficient cosine_polynomial_nonneg
    sigma sigma0 kappa t hsigma hshift hkappa
  convert h using 1
  apply sum_congr rfl
  intro k _
  simp only [mul_div_assoc, sub_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero,
    neg_div, neg_re]
  ring

/-- The shifted abscissa in equation (1.3) of Rosser--Schoenfeld (1975). -/
noncomputable def stechkinShift (sigma : ℝ) : ℝ :=
  (Real.sqrt (8 * sigma ^ 2 - 4 * sigma + 1) + 1) / 2

/-- The coefficient in equation (1.4), expressed through the canonical shifted abscissa. -/
noncomputable def stechkinFactor (sigma : ℝ) : ℝ :=
  (2 * sigma - 1) / (2 * stechkinShift sigma - 1)

lemma lt_stechkinShift (sigma : ℝ) (hsigma : 1 < sigma) :
    sigma < stechkinShift sigma := by
  have hsqrt : 2 * sigma - 1 < Real.sqrt (8 * sigma ^ 2 - 4 * sigma + 1) := by
    apply Real.lt_sqrt_of_sq_lt
    nlinarith [sq_pos_of_pos (by linarith : 0 < sigma)]
  unfold stechkinShift
  linarith

lemma stechkinFactor_pos (sigma : ℝ) (hsigma : 1 < sigma) :
    0 < stechkinFactor sigma := by
  have := lt_stechkinShift sigma hsigma
  unfold stechkinFactor
  exact div_pos (by linarith) (by linarith)

lemma stechkinFactor_lt_one (sigma : ℝ) (hsigma : 1 < sigma) :
    stechkinFactor sigma < 1 := by
  have := lt_stechkinShift sigma hsigma
  unfold stechkinFactor
  apply (div_lt_one (by linarith)).mpr
  linarith

/-- The nonnegativity conclusion of equation (1.10), with the source's quartic and Stechkin parameters.
No zero-free region, finite RH verification, or estimate for Chebyshev functions is assumed. -/
lemma stechkin_quartic_logDeriv_nonneg (sigma t : ℝ) (hsigma : 1 < sigma) :
    0 ≤ ∑ k : Fin 5, coefficient k *
      ((stechkinFactor sigma : ℂ) *
          deriv riemannZeta (stechkinShift sigma + (k : ℝ) * t * I) /
            riemannZeta (stechkinShift sigma + (k : ℝ) * t * I) -
        deriv riemannZeta (sigma + (k : ℝ) * t * I) /
          riemannZeta (sigma + (k : ℝ) * t * I)).re :=
  rosser_schoenfeld_modified_logDeriv_nonneg sigma (stechkinShift sigma)
    (stechkinFactor sigma) t hsigma (lt_stechkinShift sigma hsigma).le
    (stechkinFactor_lt_one sigma hsigma).le


end RosserSchoenfeld

theorem solution (sigma t : ℝ) (hsigma : 1 < sigma) :
    0 ≤ ∑ k : Fin 5,
      (![11.1859355312082048, 19.073344004352, 11.67618784, 4.7568, 1] : Fin 5 → ℝ) k *
        (((((2 * sigma - 1) /
              (2 * ((Real.sqrt (8 * sigma ^ 2 - 4 * sigma + 1) + 1) / 2) - 1) : ℝ) : ℂ) *
            deriv riemannZeta
              (((Real.sqrt (8 * sigma ^ 2 - 4 * sigma + 1) + 1) / 2 : ℝ) +
                (k : ℝ) * t * Complex.I) /
            riemannZeta
              (((Real.sqrt (8 * sigma ^ 2 - 4 * sigma + 1) + 1) / 2 : ℝ) +
                (k : ℝ) * t * Complex.I)) -
          deriv riemannZeta (sigma + (k : ℝ) * t * Complex.I) /
            riemannZeta (sigma + (k : ℝ) * t * Complex.I)).re := by
  simpa only [RosserSchoenfeld.coefficient, RosserSchoenfeld.stechkinFactor,
    RosserSchoenfeld.stechkinShift] using
    RosserSchoenfeld.stechkin_quartic_logDeriv_nonneg sigma t hsigma

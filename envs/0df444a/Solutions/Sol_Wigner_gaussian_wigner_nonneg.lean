-- Prove2me | solution 1 for Wigner.gaussian_wigner_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T17:51:37.837774+00:00
-- url     : https://prove2.me/submissions/7294382c-d311-4f15-bedc-9911f1ad4621

import Mathlib
import Definitions.Def_wigner

open MeasureTheory
open Wigner

open ComplexConjugate

theorem solution {a b c : ℂ} {ℏ x p : ℝ} (ha : 0 < Complex.re a)
    (hℏ : 0 < ℏ) :
    0 ≤ wigner (fun y => Complex.exp (-(a * (y : ℂ) ^ 2) + b * (y : ℂ) + c)) ℏ x p := by
  set d : ℝ := -2 * a.re * x ^ 2 + 2 * b.re * x + 2 * c.re
  set γ : ℝ := 4 * x * a.im - 2 * b.im + 2 * p / ℏ
  have hpt : ∀ y : ℝ, wignerIntegrand (fun y => Complex.exp (-(a * (y : ℂ) ^ 2) + b * (y : ℂ) + c)) ℏ x p y =
      Complex.exp (((-2 * a.re : ℝ) : ℂ) * (y : ℂ) ^ 2 + ((γ : ℂ) * Complex.I) * y + (d : ℂ)) := by
    intro y
    simp only [wignerIntegrand, ← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    apply Complex.ext
    · simp only [Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.conj_re, Complex.conj_im,
        Complex.add_im, Complex.mul_im, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, map_add, map_neg, map_mul, sq, Complex.conj_ofReal, γ, d]
      ring
    · simp only [Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.conj_re, Complex.conj_im,
        Complex.add_im, Complex.mul_im, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, map_add, map_neg, map_mul, sq, Complex.conj_ofReal, γ, d]
      field_simp
      ring
  have hB : (((-2 * a.re : ℝ) : ℂ)).re < 0 := by
    rw [Complex.ofReal_re]; linarith
  have hI : wignerIntegral (fun y => Complex.exp (-(a * (y : ℂ) ^ 2) + b * (y : ℂ) + c)) ℏ x p =
      (((Real.pi / (2 * a.re)) ^ (1 / 2 : ℝ) * Real.exp (d - γ ^ 2 / (8 * a.re)) : ℝ) : ℂ) := by
    unfold wignerIntegral
    simp only [hpt]
    rw [integral_cexp_quadratic hB]
    have hpi : ((Real.pi : ℂ) / -((-2 * a.re : ℝ) : ℂ)) = (((Real.pi / (2 * a.re)) : ℝ) : ℂ) := by
      push_cast; ring
    rw [hpi, Complex.ofReal_mul ((Real.pi / (2 * a.re)) ^ (1 / 2 : ℝ)), Complex.ofReal_cpow (by positivity)]
    congr 1
    · push_cast; ring_nf
    · rw [Complex.ofReal_exp]
      congr 1
      have ha0 : (a.re : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
      push_cast
      field_simp
      ring_nf
      rw [Complex.I_sq]
      ring
  unfold wigner
  rw [hI, Complex.ofReal_re]
  apply div_nonneg _ (by positivity)
  positivity


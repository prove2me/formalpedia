-- Prove2me | solution 1 for TaoFivePrimes.zeta_zero_free_rectangle_106_107
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T17:52:03.546762+00:00
-- url     : https://prove2.me/submissions/62769f4c-fe55-4ec0-a2e0-bdf05e07f0fb

import Mathlib.Tactic
import Theorems.Thm_TaoFivePrimes_rh106to107_xi_approximation
import Theorems.Thm_TaoFivePrimes_rh106to107_polynomial_positive

set_option autoImplicit false
open Complex

private lemma rectangle_norm (s : ℂ) (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1)
    (ha : 106 ≤ s.im) (hb : s.im ≤ 107) :
    ‖s-RH1000Analytic.CertifiedLocalXi.center (213/2)‖ ≤ 1 := by
  have hx : |s.re-1/2|≤1/2 := abs_le.mpr ⟨by linarith,by linarith⟩
  have hy : |s.im-213/2|≤1/2 := abs_le.mpr ⟨by linarith,by linarith⟩
  have h := Complex.norm_le_abs_re_add_abs_im
    (s-RH1000Analytic.CertifiedLocalXi.center (213/2))
  have he : ‖s-RH1000Analytic.CertifiedLocalXi.center (213/2)‖ ≤
      |s.re-1/2|+|s.im-213/2| := by
    simpa [RH1000Analytic.CertifiedLocalXi.center] using h
  linarith

private lemma xi_nonzero_implies_zeta {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1)
    (hXi : RH1000Analytic.CertifiedLocalXi.xi s ≠ 0) : riemannZeta s ≠ 0 := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at h0
  have hs1 : s ≠ 1 := fun h => by simp [h] at h1
  have h1s : (1:ℂ)-s ≠ 0 := sub_ne_zero.mpr hs1.symm
  rw [riemannZeta_def_of_ne_zero hs0]
  intro hz
  rcases div_eq_zero_iff.mp hz with hz | hz
  · apply hXi
    have hh := completedRiemannZeta_eq s
    rw [hz] at hh
    have hsum : completedRiemannZeta₀ s=1/s+1/(1-s) := by linear_combination -hh
    unfold RH1000Analytic.CertifiedLocalXi.xi
    rw [hsum]
    field_simp
    ring
  · exact Complex.Gammaℝ_ne_zero_of_re_pos h0 hz

theorem solution (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1)
    (ha : 106 ≤ s.im) (hb : s.im ≤ 107) : riemannZeta s ≠ 0 := by
  apply xi_nonzero_implies_zeta h0 h1
  have he := TaoFivePrimes.rh106to107_xi_approximation s
    (rectangle_norm s h0.le h1.le ha hb)
  have hp := TaoFivePrimes.rh106to107_polynomial_positive s h0.le h1.le ha hb
  intro hz
  rw [hz,mul_zero,zero_sub,norm_neg] at he
  have hreal := Complex.abs_re_le_norm
    (TaoFivePrimes_RHLocalRoundedPolynomial TaoFivePrimes_RH106To107RoundedCoefficients 40 (213/2) s)
  have hle : (TaoFivePrimes_RHLocalRoundedPolynomial TaoFivePrimes_RH106To107RoundedCoefficients
    40 (213/2) s).re ≤ |(TaoFivePrimes_RHLocalRoundedPolynomial
      TaoFivePrimes_RH106To107RoundedCoefficients 40 (213/2) s).re| := le_abs_self _
  linarith

-- Prove2me | solution 1 for TaoFivePrimes.zeta_zero_free_rectangle_108p7_109
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T18:49:47.786947+00:00
-- url     : https://prove2.me/submissions/1d2a951e-f240-433a-add2-11bc0879921f

import Mathlib.Tactic
import Theorems.Thm_TaoFivePrimes_rh106p5_xi_approximation_radius272
import Theorems.Thm_TaoFivePrimes_rh108p7to109_polynomial_negative

set_option autoImplicit false
open Complex

private lemma polynomial_eq (s : ℂ) :
    TaoFivePrimes_RHLocalRoundedPolynomial TaoFivePrimes_RH106To107RoundedCoefficients 60 (213/2) s =
      TaoFivePrimes_RHLocalRoundedPolynomial TaoFivePrimes_RH106To107RoundedCoefficients 40 (213/2) s := by
  unfold TaoFivePrimes_RHLocalRoundedPolynomial
  symm
  apply Finset.sum_subset (Finset.range_mono (by norm_num : 40 ≤ 60))
  intro n hn60 hn40
  have hge : 40 ≤ n := by simp only [Finset.mem_range] at hn40; omega
  have hz : TaoFivePrimes_RH106To107RoundedCoefficients.getD n 0 = 0 := by
    apply List.getD_eq_default
    have hlen : TaoFivePrimes_RH106To107RoundedCoefficients.length = 40 := by
      norm_num [TaoFivePrimes_RH106To107RoundedCoefficients]
    omega
  rw [hz]
  norm_num

private lemma rectangle_norm (s : ℂ) (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1)
    (ha : (1087/10:ℝ) ≤ s.im) (hb : s.im ≤ 109) :
    ‖s-RH1000Analytic.CertifiedLocalXi.center (213/2)‖ ≤ (51/20:ℝ) := by
  have hx : |s.re-1/2| ≤ 1/2 := abs_le.mpr ⟨by linarith,by linarith⟩
  have hy : |s.im-213/2| ≤ 5/2 := abs_le.mpr ⟨by linarith,by linarith⟩
  have hx2 : (s.re-1/2)^2 ≤ (1/2:ℝ)^2 := by nlinarith [abs_nonneg (s.re-1/2),sq_abs (s.re-1/2)]
  have hy2 : (s.im-213/2)^2 ≤ (5/2:ℝ)^2 := by nlinarith [abs_nonneg (s.im-213/2),sq_abs (s.im-213/2)]
  have hn : ‖s-RH1000Analytic.CertifiedLocalXi.center (213/2)‖^2 =
      (s.re-1/2)^2+(s.im-213/2)^2 := by
    rw [←Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply,RH1000Analytic.CertifiedLocalXi.center,pow_two]
  nlinarith [norm_nonneg (s-RH1000Analytic.CertifiedLocalXi.center (213/2))]

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
    (ha : (1087/10:ℝ) ≤ s.im) (hb : s.im ≤ 109) : riemannZeta s ≠ 0 := by
  apply xi_nonzero_implies_zeta h0 h1
  have he := TaoFivePrimes.rh106p5_xi_approximation_radius272 s
    (rectangle_norm s h0.le h1.le ha hb)
  rw [polynomial_eq] at he
  have hp := TaoFivePrimes.rh108p7to109_polynomial_negative s h0.le h1.le ha hb
  intro hz
  rw [hz,mul_zero,zero_sub,norm_neg] at he
  have hreal := Complex.abs_re_le_norm
    (TaoFivePrimes_RHLocalRoundedPolynomial TaoFivePrimes_RH106To107RoundedCoefficients 40 (213/2) s)
  have hle : -(TaoFivePrimes_RHLocalRoundedPolynomial TaoFivePrimes_RH106To107RoundedCoefficients
    40 (213/2) s).re ≤ |(TaoFivePrimes_RHLocalRoundedPolynomial
      TaoFivePrimes_RH106To107RoundedCoefficients 40 (213/2) s).re| := neg_le_abs _
  linarith

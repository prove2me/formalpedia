-- Prove2me | solution 1 for TaoFivePrimes.zeta_zero_free_rectangle_114p6_116
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T19:58:22.547873+00:00
-- url     : https://prove2.me/submissions/abc05f54-9934-4178-9751-7072cdcf1bbf

import Mathlib.Tactic
import Theorems.Thm_TaoFivePrimes_rh114p5_xi_approximation
import Theorems.Thm_TaoFivePrimes_rh114p6to116_polynomial_positive

set_option autoImplicit false
open Complex

private lemma polynomial_eq (s : ℂ) :
    TaoFivePrimes_RHLocalRoundedPolynomial TaoFivePrimes_RH114p5RoundedCoefficients 60 (229/2) s =
      TaoFivePrimes_RHLocalRoundedPolynomial TaoFivePrimes_RH114p5RoundedCoefficients 40 (229/2) s := by
  unfold TaoFivePrimes_RHLocalRoundedPolynomial
  symm
  apply Finset.sum_subset (Finset.range_mono (by norm_num : 40 ≤ 60))
  intro n hn60 hn40
  have hge : 40 ≤ n := by simp only [Finset.mem_range] at hn40; omega
  have hz : TaoFivePrimes_RH114p5RoundedCoefficients.getD n 0 = 0 := by
    apply List.getD_eq_default
    have hlen : TaoFivePrimes_RH114p5RoundedCoefficients.length = 40 := by
      norm_num [TaoFivePrimes_RH114p5RoundedCoefficients]
    omega
  rw [hz]
  norm_num

private lemma rectangle_norm (s : ℂ) (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1)
    (ha : (573/5:ℝ) ≤ s.im) (hb : s.im ≤ (116:ℝ)) :
    ‖s-RH1000Analytic.CertifiedLocalXi.center (229/2)‖ ≤ (5/2:ℝ) := by
  have hx : |s.re-1/2| ≤ 1/2 := abs_le.mpr ⟨by linarith,by linarith⟩
  have hy : |s.im-229/2| ≤ 3/2 := abs_le.mpr ⟨by linarith,by linarith⟩
  have hx2 : (s.re-1/2)^2 ≤ (1/2:ℝ)^2 := by nlinarith [abs_nonneg (s.re-1/2),sq_abs (s.re-1/2)]
  have hy2 : (s.im-229/2)^2 ≤ (3/2:ℝ)^2 := by nlinarith [abs_nonneg (s.im-229/2),sq_abs (s.im-229/2)]
  have hn : ‖s-RH1000Analytic.CertifiedLocalXi.center (229/2)‖^2 =
      (s.re-1/2)^2+(s.im-229/2)^2 := by
    rw [←Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply,RH1000Analytic.CertifiedLocalXi.center,pow_two]
  nlinarith [norm_nonneg (s-RH1000Analytic.CertifiedLocalXi.center (229/2))]

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
    (ha : (573/5:ℝ) ≤ s.im) (hb : s.im ≤ (116:ℝ)) : riemannZeta s ≠ 0 := by
  apply xi_nonzero_implies_zeta h0 h1
  have he := TaoFivePrimes.rh114p5_xi_approximation s
    (rectangle_norm s h0.le h1.le ha hb)
  rw [polynomial_eq] at he
  have hp := TaoFivePrimes.rh114p6to116_polynomial_positive s h0.le h1.le ha hb
  intro hz
  rw [hz,mul_zero,zero_sub,norm_neg] at he
  have hreal := Complex.abs_re_le_norm
    (TaoFivePrimes_RHLocalRoundedPolynomial TaoFivePrimes_RH114p5RoundedCoefficients 40 (229/2) s)
  have hle : (TaoFivePrimes_RHLocalRoundedPolynomial TaoFivePrimes_RH114p5RoundedCoefficients
    40 (229/2) s).re ≤ |(TaoFivePrimes_RHLocalRoundedPolynomial
      TaoFivePrimes_RH114p5RoundedCoefficients 40 (229/2) s).re| := le_abs_self _
  linarith

-- Prove2me | solution 1 for TaoFivePrimes.zeta_zero_free_rectangle_131p15_133p2
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:36:06.753339+00:00
-- url     : https://prove2.me/submissions/52df6a16-bcb2-4ec5-b8a9-a325f82d14ff

import Mathlib.Tactic
import Theorems.Thm_TaoFivePrimes_rh132_xi_approximation
import Theorems.Thm_TaoFivePrimes_rh131p15to133p2_polynomial_positive

set_option autoImplicit false
open Complex

private lemma polynomial_eq (s : ℂ) :
    TaoFivePrimes_RHLocalRationalPolynomial TaoFivePrimes_RH132RoundedCoefficients14 (10^14) 60 132 s =
      TaoFivePrimes_RHLocalRationalPolynomial TaoFivePrimes_RH132RoundedCoefficients14 (10^14) 40 132 s := by
  unfold TaoFivePrimes_RHLocalRationalPolynomial
  symm
  apply Finset.sum_subset (Finset.range_mono (by norm_num : 40 ≤ 60))
  intro n hn60 hn40
  have hge : 40 ≤ n := by simp only [Finset.mem_range] at hn40; omega
  have hz : TaoFivePrimes_RH132RoundedCoefficients14.getD n 0 = 0 := by
    apply List.getD_eq_default
    have hlen : TaoFivePrimes_RH132RoundedCoefficients14.length = 40 := by
      norm_num [TaoFivePrimes_RH132RoundedCoefficients14]
    omega
  rw [hz]
  norm_num

private lemma rectangle_norm (s : ℂ) (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1)
    (ha : (2623/20:ℝ) ≤ s.im) (hb : s.im ≤ (666/5:ℝ)) :
    ‖s-RH1000Analytic.CertifiedLocalXi.center 132‖ ≤ (31/10:ℝ) := by
  have hx : |s.re-1/2| ≤ 1/2 := abs_le.mpr ⟨by linarith,by linarith⟩
  have hy : |s.im-132| ≤ 6/5 := abs_le.mpr ⟨by linarith,by linarith⟩
  have hx2 : (s.re-1/2)^2 ≤ (1/2:ℝ)^2 := by nlinarith [abs_nonneg (s.re-1/2),sq_abs (s.re-1/2)]
  have hy2 : (s.im-132)^2 ≤ (6/5:ℝ)^2 := by nlinarith [abs_nonneg (s.im-132),sq_abs (s.im-132)]
  have hn : ‖s-RH1000Analytic.CertifiedLocalXi.center 132‖^2 =
      (s.re-1/2)^2+(s.im-132)^2 := by
    rw [←Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply,RH1000Analytic.CertifiedLocalXi.center,pow_two]
  nlinarith [norm_nonneg (s-RH1000Analytic.CertifiedLocalXi.center 132)]

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
    (ha : (2623/20:ℝ) ≤ s.im) (hb : s.im ≤ (666/5:ℝ)) : riemannZeta s ≠ 0 := by
  apply xi_nonzero_implies_zeta h0 h1
  have he := TaoFivePrimes.rh132_xi_approximation s
    (rectangle_norm s h0.le h1.le ha hb)
  rw [polynomial_eq] at he
  have hp := TaoFivePrimes.rh131p15to133p2_polynomial_positive s h0.le h1.le ha hb
  rw [show (264/2:ℝ)=132 by norm_num] at hp
  intro hz
  rw [hz,mul_zero,zero_sub,norm_neg] at he
  have hreal := Complex.abs_re_le_norm
    (TaoFivePrimes_RHLocalRationalPolynomial TaoFivePrimes_RH132RoundedCoefficients14 (10^14) 40 132 s)
  have hle : (TaoFivePrimes_RHLocalRationalPolynomial TaoFivePrimes_RH132RoundedCoefficients14 (10^14)
    40 132 s).re ≤ |(TaoFivePrimes_RHLocalRationalPolynomial
      TaoFivePrimes_RH132RoundedCoefficients14 (10^14) 40 132 s).re| := le_abs_self _
  have hbad : (4:ℝ) ≤ 27/1000 := hp.trans (hle.trans (hreal.trans he))
  norm_num at hbad

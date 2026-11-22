-- Prove2me | solution 1 for TaoFivePrimes.zeta_zero_free_rectangle_133p8_134p4
-- status  : ACCEPTED   (prove)
-- author  : @phi9t
-- created : 2026-11-22T23:06:46.826199+00:00
-- url     : https://prove2.me/submissions/5faa5d1e-c657-4e89-8fb7-bd15de3dd54a

/-
Nonvanishing of the Riemann zeta function for 0 < Re(s) < 1 and
669/5 ≤ Im(s) ≤ 672/5.

Adapted from Johan Mercedes' accepted neighboring rectangle proof
(submission 52df6a16-bcb2-4ec5-b8a9-a325f82d14ff), using the accepted
TaoFivePrimes.rh133p8to134p4_polynomial_negative certificate.
The imported xi approximation, coefficient data, and theta/Mellin foundations
retain their prior attributions to Johan Mercedes, sometik179, and Gabewhigham.
-/
import Mathlib.Data.List.GetD
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Theorems.Thm_TaoFivePrimes_rh132_xi_approximation
import Theorems.Thm_TaoFivePrimes_rh133p8to134p4_polynomial_negative

set_option autoImplicit false
open Complex

private lemma polynomial_eq (s : ℂ) :
    TaoFivePrimes_RHLocalRationalPolynomial TaoFivePrimes_RH132RoundedCoefficients14
      (10^14) 60 132 s =
    TaoFivePrimes_RHLocalRationalPolynomial TaoFivePrimes_RH132RoundedCoefficients14
      (10^14) 40 132 s := by
  unfold TaoFivePrimes_RHLocalRationalPolynomial
  symm
  apply Finset.sum_subset (Finset.range_mono (by norm_num : 40 ≤ 60))
  intro n hn60 hn40
  have hge : 40 ≤ n := Nat.le_of_not_gt (fun h => hn40 (Finset.mem_range.mpr h))
  have hz : TaoFivePrimes_RH132RoundedCoefficients14.getD n 0 = 0 := by
    apply List.getD_eq_default
    have hlen : TaoFivePrimes_RH132RoundedCoefficients14.length = 40 := by
      norm_num [TaoFivePrimes_RH132RoundedCoefficients14]
    simpa only [hlen] using hge
  rw [hz]
  norm_num

private lemma rectangle_norm (s : ℂ) (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1)
    (ha : (669/5:ℝ) ≤ s.im) (hb : s.im ≤ (672/5:ℝ)) :
    ‖s-RH1000Analytic.CertifiedLocalXi.center 132‖ ≤ (31/10:ℝ) := by
  have hx : |s.re-1/2| ≤ 1/2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hy : |s.im-132| ≤ 12/5 := abs_le.mpr ⟨by linarith, by linarith⟩
  calc
    ‖s-RH1000Analytic.CertifiedLocalXi.center 132‖ ≤
        |s.re-1/2| + |s.im-132| := by
      simpa [RH1000Analytic.CertifiedLocalXi.center] using
        Complex.norm_le_abs_re_add_abs_im
          (s-RH1000Analytic.CertifiedLocalXi.center 132)
    _ ≤ (1/2:ℝ) + 12/5 := add_le_add hx hy
    _ ≤ (31/10:ℝ) := by norm_num

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
    have hsum : completedRiemannZeta₀ s = 1/s + 1/(1-s) := by
      linear_combination -hh
    unfold RH1000Analytic.CertifiedLocalXi.xi
    rw [hsum]
    field_simp
    ring
  · exact Complex.Gammaℝ_ne_zero_of_re_pos h0 hz

theorem solution (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1)
    (ha : (669/5:ℝ) ≤ s.im) (hb : s.im ≤ (672/5:ℝ)) : riemannZeta s ≠ 0 := by
  apply xi_nonzero_implies_zeta h0 h1
  have he := TaoFivePrimes.rh132_xi_approximation s
    (rectangle_norm s h0.le h1.le ha hb)
  rw [polynomial_eq] at he
  have hp := TaoFivePrimes.rh133p8to134p4_polynomial_negative
    s h0.le h1.le ha hb
  rw [show (264/2:ℝ) = 132 by norm_num] at hp
  intro hz
  rw [hz, mul_zero, zero_sub, norm_neg] at he
  have hreal := Complex.abs_re_le_norm
    (TaoFivePrimes_RHLocalRationalPolynomial TaoFivePrimes_RH132RoundedCoefficients14
      (10^14) 40 132 s)
  have hle :
      -(TaoFivePrimes_RHLocalRationalPolynomial TaoFivePrimes_RH132RoundedCoefficients14
        (10^14) 40 132 s).re ≤
      |(TaoFivePrimes_RHLocalRationalPolynomial TaoFivePrimes_RH132RoundedCoefficients14
        (10^14) 40 132 s).re| := neg_le_abs _
  have hbad : (6:ℝ) ≤ 27/1000 := hp.trans (hle.trans (hreal.trans he))
  norm_num at hbad

#check solution
#print axioms solution

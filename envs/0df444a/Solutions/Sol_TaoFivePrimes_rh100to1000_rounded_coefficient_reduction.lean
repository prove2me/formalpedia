-- Prove2me | solution 1 for TaoFivePrimes.rh100to1000_rounded_coefficient_reduction
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-14T06:05:17.087592+00:00
-- url     : https://prove2.me/submissions/e47f6892-3916-490f-90f5-a27d73451329

import Theorems.Thm_TaoFivePrimes_rh100to1000_xi_polynomial_error
import Definitions.Def_TaoFivePrimes_RHLocalRoundedPolynomial
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
namespace RHRoundedReduction
open Complex Finset
lemma rotation (d : ℂ) (n : ℕ) : Complex.I^n*(-Complex.I*d)^n=d^n := by
  rw [←mul_pow]
  congr 1
  calc
    Complex.I*(-Complex.I*d)=-(Complex.I*Complex.I)*d := by ring
    _=d := by rw [Complex.I_mul_I]; ring
lemma finite_rounding (T : ℝ) (S : ℕ) (v : List ℤ)
    (hdata : ∀ n < 272, ‖(S:ℂ)*TaoFivePrimes_RH100To1000XiCoefficient T n*Complex.I^n-
      ((v.getD n 0:ℝ)/(10^8:ℝ):ℂ)‖ ≤ 1/10^6)
    (z : ℂ) (hz : ‖z-RH1000Analytic.CertifiedLocalXi.center T‖ ≤ 1) :
    ‖(S:ℂ)*TaoFivePrimes_RH100To1000XiPolynomial T z-
      TaoFivePrimes_RHLocalRoundedPolynomial v 272 T z‖ ≤ 272/10^6 := by
  have hw : ‖-Complex.I*(z-RH1000Analytic.CertifiedLocalXi.center T)‖ ≤ 1 := by
    simpa only [norm_mul,norm_neg,Complex.norm_I,one_mul] using hz
  unfold TaoFivePrimes_RH100To1000XiPolynomial TaoFivePrimes_RHLocalRoundedPolynomial
  rw [mul_sum,←sum_sub_distrib]
  calc
    _ ≤ ∑ n ∈ range 272, ‖(S:ℂ)*(TaoFivePrimes_RH100To1000XiCoefficient T n*
       (z-RH1000Analytic.CertifiedLocalXi.center T)^n)-
       ((v.getD n 0:ℝ)/(10^8:ℝ):ℂ)*(-Complex.I*(z-RH1000Analytic.CertifiedLocalXi.center T))^n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ range 272, (1/10^6:ℝ) := by
      apply sum_le_sum
      intro n hn
      have he : (S:ℂ)*(TaoFivePrimes_RH100To1000XiCoefficient T n*(z-RH1000Analytic.CertifiedLocalXi.center T)^n)-
         ((v.getD n 0:ℝ)/(10^8:ℝ):ℂ)*(-Complex.I*(z-RH1000Analytic.CertifiedLocalXi.center T))^n=
        ((S:ℂ)*TaoFivePrimes_RH100To1000XiCoefficient T n*Complex.I^n-
          ((v.getD n 0:ℝ)/(10^8:ℝ):ℂ))*(-Complex.I*(z-RH1000Analytic.CertifiedLocalXi.center T))^n := by
        rw [sub_mul, mul_assoc, rotation]
        ring
      rw [he,norm_mul,norm_pow]
      calc
        _ ≤ (1/10^6:ℝ)*1 := mul_le_mul (hdata n (mem_range.mp hn))
          (pow_le_one₀ (norm_nonneg _) hw) (by positivity) (by positivity)
        _=_ := by ring
    _=_ := by norm_num
lemma rounded_error (T : ℝ) (hT : |T| ≤ 1000) (S : ℕ) (hS : S ≤ 10^350)
    (v : List ℤ)
    (hdata : ∀ n < 272, ‖(S:ℂ)*TaoFivePrimes_RH100To1000XiCoefficient T n*Complex.I^n-
      ((v.getD n 0:ℝ)/(10^8:ℝ):ℂ)‖ ≤ 1/10^6)
    (z : ℂ) (hz : ‖z-RH1000Analytic.CertifiedLocalXi.center T‖ ≤ 1) :
    ‖(S:ℂ)*RH1000Analytic.CertifiedLocalXi.xi z-
      TaoFivePrimes_RHLocalRoundedPolynomial v 272 T z‖ ≤ 1/100 := by
  have hs : (S:ℝ) ≤ 10^350 := by exact_mod_cast hS
  have ha := TaoFivePrimes.rh100to1000_xi_polynomial_error T hT z hz
  have hr := finite_rounding T S v hdata z hz
  have he : (S:ℂ)*RH1000Analytic.CertifiedLocalXi.xi z-TaoFivePrimes_RHLocalRoundedPolynomial v 272 T z=
    (S:ℂ)*(RH1000Analytic.CertifiedLocalXi.xi z-TaoFivePrimes_RH100To1000XiPolynomial T z)+
      ((S:ℂ)*TaoFivePrimes_RH100To1000XiPolynomial T z-TaoFivePrimes_RHLocalRoundedPolynomial v 272 T z) := by ring
  rw [he]
  apply (norm_add_le _ _).trans
  rw [norm_mul,Complex.norm_natCast]
  calc
    _ ≤ (10^350:ℝ)*(1/10^356)+272/10^6 := add_le_add
      (mul_le_mul hs ha (by positivity) (by positivity)) hr
    _ ≤ _ := by norm_num
end RHRoundedReduction

theorem solution (T : ℝ) (hT : |T| ≤ 1000) (S : ℕ) (hS : S ≤ 10^350)
    (v : List ℤ)
    (hdata : ∀ n < 272, ‖(S:ℂ)*TaoFivePrimes_RH100To1000XiCoefficient T n*Complex.I^n-
      ((v.getD n 0:ℝ)/(10^8:ℝ):ℂ)‖ ≤ 1/10^6)
    (z : ℂ) (hz : ‖z-RH1000Analytic.CertifiedLocalXi.center T‖ ≤ 1) :
    ‖(S:ℂ)*RH1000Analytic.CertifiedLocalXi.xi z-
      TaoFivePrimes_RHLocalRoundedPolynomial v 272 T z‖ ≤ 1/100 := RHRoundedReduction.rounded_error T hT S hS v hdata z hz

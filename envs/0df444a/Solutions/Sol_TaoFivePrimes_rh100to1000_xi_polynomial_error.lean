-- Prove2me | solution 1 for TaoFivePrimes.rh100to1000_xi_polynomial_error
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-14T06:03:06.045783+00:00
-- url     : https://prove2.me/submissions/9c827213-dd4f-4872-b249-c0cbe9ca45b2

import Mathlib
import Theorems.Thm_TaoFivePrimes_rh100to1000_xi_coefficient_error
import Theorems.Thm_TaoFivePrimes_rh100to1000_local_taylor_remainder
import Definitions.Def_TaoFivePrimes_RH100To1000XiPolynomial
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
namespace RHXiPolynomialEnclosure
open Complex Finset
lemma finite_error (T : ℝ) (hT : |T| ≤ 1000) (z : ℂ)
    (hz : ‖z-RH1000Analytic.CertifiedLocalXi.center T‖ ≤ 1) :
    ‖RH1000Analytic.CertifiedComplexTaylor.polynomial RH1000Analytic.CertifiedLocalXi.xi
        (RH1000Analytic.CertifiedLocalXi.center T) 272 z-
      TaoFivePrimes_RH100To1000XiPolynomial T z‖ ≤ 272/10^359 := by
  unfold RH1000Analytic.CertifiedComplexTaylor.polynomial TaoFivePrimes_RH100To1000XiPolynomial
  rw [←sum_sub_distrib]
  calc
    _ ≤ ∑ n ∈ range 272, ‖RH1000Analytic.CertifiedTaylorQuadrature.coefficient
      RH1000Analytic.CertifiedLocalXi.xi (RH1000Analytic.CertifiedLocalXi.center T) n*
        (z-RH1000Analytic.CertifiedLocalXi.center T)^n-
      TaoFivePrimes_RH100To1000XiCoefficient T n*(z-RH1000Analytic.CertifiedLocalXi.center T)^n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ range 272, (1/10^359:ℝ) := by
      apply sum_le_sum
      intro n _
      rw [←sub_mul,norm_mul,norm_pow]
      have hp : ‖z-RH1000Analytic.CertifiedLocalXi.center T‖^n ≤ 1 :=
        pow_le_one₀ (norm_nonneg _) hz
      calc
        _ ≤ (1/10^359:ℝ)*1 := mul_le_mul
          (TaoFivePrimes.rh100to1000_xi_coefficient_error T hT n) hp (by positivity) (by positivity)
        _ = _ := by ring
    _ = _ := by norm_num
lemma polynomial_error (T : ℝ) (hT : |T| ≤ 1000) (z : ℂ)
    (hz : ‖z-RH1000Analytic.CertifiedLocalXi.center T‖ ≤ 1) :
    ‖RH1000Analytic.CertifiedLocalXi.xi z-TaoFivePrimes_RH100To1000XiPolynomial T z‖ ≤ 1/10^356 := by
  have ht := TaoFivePrimes.rh100to1000_local_taylor_remainder T hT z hz
  have hp := finite_error T hT z hz
  have he : RH1000Analytic.CertifiedLocalXi.xi z-TaoFivePrimes_RH100To1000XiPolynomial T z=
    RH1000Analytic.CertifiedComplexTaylor.remainder RH1000Analytic.CertifiedLocalXi.xi
      (RH1000Analytic.CertifiedLocalXi.center T) 272 z+
    (RH1000Analytic.CertifiedComplexTaylor.polynomial RH1000Analytic.CertifiedLocalXi.xi
      (RH1000Analytic.CertifiedLocalXi.center T) 272 z-TaoFivePrimes_RH100To1000XiPolynomial T z) := by
    unfold RH1000Analytic.CertifiedComplexTaylor.remainder
    ring
  rw [he]
  apply (norm_add_le _ _).trans
  calc
    _ ≤ (1/10^365:ℝ)+272/10^359 := add_le_add ht hp
    _ ≤ _ := by norm_num
end RHXiPolynomialEnclosure

theorem solution (T : ℝ) (hT : |T| ≤ 1000) (z : ℂ)
    (hz : ‖z-RH1000Analytic.CertifiedLocalXi.center T‖ ≤ 1) :
    ‖RH1000Analytic.CertifiedLocalXi.xi z-TaoFivePrimes_RH100To1000XiPolynomial T z‖ ≤ 1/10^356 := RHXiPolynomialEnclosure.polynomial_error T hT z hz

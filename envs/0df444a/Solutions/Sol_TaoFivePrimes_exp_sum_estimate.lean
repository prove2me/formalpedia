-- Prove2me | solution 1 for TaoFivePrimes.exp_sum_estimate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-09T12:01:18.042538+00:00
-- url     : https://prove2.me/submissions/7f57f27d-621c-4e75-b092-baef97bbeb0f

import Theorems.Thm_TaoFivePrimes_exp_sum_estimate_section6_source_envelope
import Mathlib.Analysis.Complex.ExponentialBounds

open TaoFivePrimes

set_option maxHeartbeats 800000

theorem solution (x alpha beta : ℝ) (a : ℤ) (q q0 : ℕ)
    (hx : (10 : ℝ) ^ 20 ≤ x)
    (hq : 100 ≤ q) (hqx : (q : ℝ) ≤ x / 100)
    (haq : Nat.Coprime a.natAbs q)
    (halpha : 4 * alpha = (a : ℝ) / q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (hq0 : ∀ p ∈ q0.primeFactors, (p : ℝ) ≤ Real.sqrt x) :
    ‖smoothedExpSum eta0 q0 x alpha‖ ≤
      (0.14 * x / Real.sqrt q + 0.64 * x / Real.sqrt (x / q) +
          0.15 * x ^ (4 / 5 : ℝ)) *
        Real.log x * (Real.log x + 11.3) := by
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hxnonneg : 0 ≤ x := hxpos.le
  have hqpos_nat : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hqpos_nat
  have hqnonneg : (0 : ℝ) ≤ q := hqpos.le
  have hq100 : (100 : ℝ) ≤ q := by exact_mod_cast hq
  have hwpos : 0 < x / (q : ℝ) := div_pos hxpos hqpos
  have hwnonneg : 0 ≤ x / (q : ℝ) := hwpos.le

  have hexp_two_le_ten : Real.exp 2 ≤ (10 : ℝ) := by
    calc
      Real.exp 2 = Real.exp 1 ^ (2 : ℕ) := by
        rw [← Real.exp_nat_mul]
        norm_num
      _ ≤ (3 : ℝ) ^ (2 : ℕ) :=
        (pow_lt_pow_left₀ Real.exp_one_lt_three (Real.exp_pos 1).le
          (by norm_num)).le
      _ ≤ 10 := by norm_num
  have hlog_ten_two : (2 : ℝ) ≤ Real.log 10 :=
    (Real.le_log_iff_exp_le (by norm_num)).2 hexp_two_le_ten
  have hlogmono : Real.log ((10 : ℝ) ^ 20) ≤ Real.log x :=
    Real.log_le_log (by positivity) hx
  rw [Real.log_pow] at hlogmono
  norm_num at hlogmono
  have hlogx40 : (40 : ℝ) ≤ Real.log x := by nlinarith
  have hlogx_nonneg : 0 ≤ Real.log x := by linarith
  have hlogprod_nonneg :
      0 ≤ Real.log x * (Real.log x + 11.3) := by positivity
  have hlogprod_one :
      (1 : ℝ) ≤ Real.log x * (Real.log x + 11.3) := by
    nlinarith [sq_nonneg (Real.log x - 40)]

  have hsqrtq_nonneg : 0 ≤ Real.sqrt (q : ℝ) := Real.sqrt_nonneg _
  have hsqrtq_sq : Real.sqrt (q : ℝ) ^ 2 = (q : ℝ) :=
    Real.sq_sqrt hqnonneg
  have hsqrtq_ten : (10 : ℝ) ≤ Real.sqrt q := by
    nlinarith [sq_nonneg (Real.sqrt (q : ℝ) - 10)]
  have hten_sqrtq_le_q :
      10 * Real.sqrt (q : ℝ) ≤ (q : ℝ) := by
    nlinarith
  have hxq_absorb_base :
      x / (q : ℝ) ≤ 0.1 * (x / Real.sqrt q) := by
    calc
      x / (q : ℝ) ≤ x / (10 * Real.sqrt q) :=
        div_le_div₀ hxnonneg le_rfl (by positivity) hten_sqrtq_le_q
      _ = 0.1 * (x / Real.sqrt q) := by ring
  have hxq_absorb :
      0.4 * (x / (q : ℝ)) ≤ 0.04 * (x / Real.sqrt q) := by
    nlinarith

  have h100q_le_x : (100 : ℝ) * q ≤ x := by
    have h := (le_div_iff₀ (by norm_num : (0 : ℝ) < 100)).1 hqx
    nlinarith
  have hw100 : (100 : ℝ) ≤ x / (q : ℝ) :=
    (le_div_iff₀ hqpos).2 (by nlinarith)
  have hsqrtw_nonneg : 0 ≤ Real.sqrt (x / (q : ℝ)) := Real.sqrt_nonneg _
  have hsqrtw_sq : Real.sqrt (x / (q : ℝ)) ^ 2 = x / (q : ℝ) :=
    Real.sq_sqrt hwnonneg
  have hsqrtw_ten : (10 : ℝ) ≤ Real.sqrt (x / q) := by
    nlinarith [sq_nonneg (Real.sqrt (x / (q : ℝ)) - 10)]
  have hten_sqrtw_le_w :
      10 * Real.sqrt (x / (q : ℝ)) ≤ x / (q : ℝ) := by
    nlinarith
  have hxw_absorb_base :
      x / (x / (q : ℝ)) ≤
        0.1 * (x / Real.sqrt (x / q)) := by
    calc
      x / (x / (q : ℝ)) ≤
          x / (10 * Real.sqrt (x / q)) :=
        div_le_div₀ hxnonneg le_rfl (by positivity) hten_sqrtw_le_w
      _ = 0.1 * (x / Real.sqrt (x / q)) := by ring
  have hxw_absorb :
      2.45 * (x / (x / (q : ℝ))) ≤
        0.245 * (x / Real.sqrt (x / q)) := by
    nlinarith

  have hpoly :
      0.4 * (x / (q : ℝ)) + 0.1 * (x / Real.sqrt q) +
          2.45 * (x / (x / (q : ℝ))) +
          0.39 * (x / Real.sqrt (x / q)) +
          0.149 * x ^ (4 / 5 : ℝ) ≤
        0.14 * (x / Real.sqrt q) +
          0.635 * (x / Real.sqrt (x / q)) +
          0.149 * x ^ (4 / 5 : ℝ) := by
    linarith
  have hscaled := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hpoly hlogx_nonneg)
    (by linarith : 0 ≤ Real.log x + 11.3)

  have hx_three_tenths :
      (10 : ℝ) ^ 6 ≤ x ^ (3 / 10 : ℝ) := by
    calc
      (10 : ℝ) ^ 6 = (((10 : ℝ) ^ 20) ^ (3 / 10 : ℝ)) := by
        symm
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10)]
        norm_num
      _ ≤ x ^ (3 / 10 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hx (by norm_num)
  have hsqrtx_nonneg : 0 ≤ Real.sqrt x := Real.sqrt_nonneg _
  have hx_scale :
      (10 : ℝ) ^ 6 * Real.sqrt x ≤ x ^ (4 / 5 : ℝ) := by
    calc
      (10 : ℝ) ^ 6 * Real.sqrt x ≤
          x ^ (3 / 10 : ℝ) * Real.sqrt x := by gcongr
      _ = Real.sqrt x * x ^ (3 / 10 : ℝ) := by ring
      _ = x ^ (4 / 5 : ℝ) := by
        rw [Real.sqrt_eq_rpow]
        rw [← Real.rpow_add hxpos]
        norm_num
  have herror :
      20.16 * Real.sqrt x ≤
        0.001 * x ^ (4 / 5 : ℝ) *
          (Real.log x * (Real.log x + 11.3)) := by
    calc
      20.16 * Real.sqrt x ≤
          0.001 * ((10 : ℝ) ^ 6 * Real.sqrt x) * 1 := by
        norm_num
        nlinarith
      _ ≤ 0.001 * x ^ (4 / 5 : ℝ) *
          (Real.log x * (Real.log x + 11.3)) := by gcongr

  have hsource :=
    TaoFivePrimes.exp_sum_estimate_section6_source_envelope
      x alpha beta a q q0 hx hq hqx haq halpha hbeta hq0
  calc
    ‖smoothedExpSum eta0 q0 x alpha‖ ≤
        (0.4 * (x / q) + 0.1 * (x / Real.sqrt q) +
            2.45 * (x / (x / q)) +
            0.39 * (x / Real.sqrt (x / q)) +
            0.149 * x ^ (4 / 5 : ℝ)) *
          Real.log x * (Real.log x + 11.3) +
        20.16 * Real.sqrt x := hsource
    _ ≤ (0.14 * (x / Real.sqrt q) +
            0.635 * (x / Real.sqrt (x / q)) +
            0.149 * x ^ (4 / 5 : ℝ)) *
          Real.log x * (Real.log x + 11.3) +
        0.001 * x ^ (4 / 5 : ℝ) *
          (Real.log x * (Real.log x + 11.3)) := by
      linarith
    _ = (0.14 * (x / Real.sqrt q) +
            0.635 * (x / Real.sqrt (x / q)) +
            0.15 * x ^ (4 / 5 : ℝ)) *
          Real.log x * (Real.log x + 11.3) := by ring
    _ ≤ (0.14 * (x / Real.sqrt q) +
            0.64 * (x / Real.sqrt (x / q)) +
            0.15 * x ^ (4 / 5 : ℝ)) *
          Real.log x * (Real.log x + 11.3) := by
      have htail_nonneg :
          0 ≤ (x / Real.sqrt (x / q)) *
            (Real.log x * (Real.log x + 11.3)) := by positivity
      nlinarith
    _ = (0.14 * x / Real.sqrt q +
            0.64 * x / Real.sqrt (x / q) +
            0.15 * x ^ (4 / 5 : ℝ)) *
          Real.log x * (Real.log x + 11.3) := by ring

#print axioms solution

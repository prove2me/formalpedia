-- Prove2me | solution 1 for TaoFivePrimes.exp_sum_estimate_small_q
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-09T11:01:24.525989+00:00
-- url     : https://prove2.me/submissions/4f2fc311-971f-4b0f-90f1-4e5c4c7300a0

import Theorems.Thm_TaoFivePrimes_exp_sum_estimate_small_q_source_envelope
import Mathlib.Analysis.Complex.ExponentialBounds

open TaoFivePrimes

namespace TaoFivePrimes

private theorem log_three_halves_le_three_fifths :
    Real.log ((3 : ℝ) / 2) ≤ (3 : ℝ) / 5 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  calc
    (3 : ℝ) / 2 ≤ ∑ i ∈ Finset.range 3,
        ((3 : ℝ) / 5) ^ i / Nat.factorial i := by
      norm_num [Finset.sum_range_succ]
    _ ≤ Real.exp ((3 : ℝ) / 5) :=
      Real.sum_le_exp_of_nonneg (by norm_num) 3

end TaoFivePrimes

theorem solution (x alpha beta : ℝ) (a : ℤ) (q q0 : ℕ)
    (hx : (10 : ℝ) ^ 20 ≤ x)
    (hq : 100 ≤ q) (hqx : (q : ℝ) ≤ x / 100)
    (haq : Nat.Coprime a.natAbs q)
    (halpha : 4 * alpha = (a : ℝ) / q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (hq0 : ∀ p ∈ q0.primeFactors, (p : ℝ) ≤ Real.sqrt x)
    (hsmall : (q : ℝ) ≤ x ^ (1 / 3 : ℝ)) :
    ‖smoothedExpSum eta0 q0 x alpha‖ ≤
      0.5 * (x / q) * Real.log (2 * x) * (Real.log (2 * x) + 15)
        + 0.31 * (x / Real.sqrt q) * Real.log q *
          (Real.log q + 8.9) := by
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hxnonneg : 0 ≤ x := hxpos.le
  have hqpos_nat : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hqpos_nat
  have hqnonneg : (0 : ℝ) ≤ q := hqpos.le
  have hqone : (1 : ℝ) ≤ q := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hqpos_nat.ne')
  have hq100 : (100 : ℝ) ≤ q := by exact_mod_cast hq
  have hlogq_nonneg : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hqone
  have hlog2x_nonneg : 0 ≤ Real.log (2 * x) :=
    Real.log_nonneg (by nlinarith)
  have hqcube : (q : ℝ) ^ 3 ≤ x := by
    calc
      (q : ℝ) ^ 3 ≤ (x ^ (1 / 3 : ℝ)) ^ 3 :=
        pow_le_pow_left₀ hqnonneg hsmall 3
      _ = x := by
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul hxnonneg]
        norm_num
  have hfour_qsq : 4 * (q : ℝ) ^ 2 ≤ x := by
    calc
      4 * (q : ℝ) ^ 2 ≤ (q : ℝ) * (q : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith : (4 : ℝ) ≤ q) (sq_nonneg _)
      _ = (q : ℝ) ^ 3 := by ring
      _ ≤ x := hqcube
  have hlog_three : Real.log (3 : ℝ) ≤ Real.log 2 + 3 / 5 := by
    calc
      Real.log (3 : ℝ) = Real.log ((3 : ℝ) / 2) + Real.log 2 := by
        rw [← Real.log_mul (by norm_num : (3 : ℝ) / 2 ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
        norm_num
      _ ≤ 3 / 5 + Real.log 2 := by
        linarith [TaoFivePrimes.log_three_halves_le_three_fifths]
      _ = Real.log 2 + 3 / 5 := by ring
  have hsum : 2 * x + 4 * (q : ℝ) ^ 2 ≤ 3 * x := by linarith
  have hlogsum :
      Real.log (2 * x + 4 * (q : ℝ) ^ 2) + 14.4 ≤
        Real.log (2 * x) + 15 := by
    have hmono : Real.log (2 * x + 4 * (q : ℝ) ^ 2) ≤ Real.log (3 * x) :=
      Real.log_le_log (by positivity) hsum
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hxpos.ne'] at hmono
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hxpos.ne']
    linarith
  have hrawlog :
      0.5 * Real.log (2 * x / (q : ℝ) ^ 2 + 4) +
          0.9 * (8 + Real.log q) ≤
        0.5 * (Real.log (2 * x) + 15) := by
    have hrewrite :
        Real.log (2 * x / (q : ℝ) ^ 2 + 4) =
          Real.log (2 * x + 4 * (q : ℝ) ^ 2) -
            2 * Real.log (q : ℝ) := by
      rw [show 2 * x / (q : ℝ) ^ 2 + 4 =
          (2 * x + 4 * (q : ℝ) ^ 2) / (q : ℝ) ^ 2 by
            field_simp]
      rw [Real.log_div (by positivity) (by positivity), Real.log_pow]
      norm_num
    rw [hrewrite]
    nlinarith [hlogsum, hlogq_nonneg]
  have hfirst :
      (x / q) * Real.log (2 * x) *
          (0.5 * Real.log (2 * x / (q : ℝ) ^ 2 + 4) +
            0.9 * (8 + Real.log q)) ≤
        0.5 * (x / q) * Real.log (2 * x) *
          (Real.log (2 * x) + 15) := by
    calc
      (x / q) * Real.log (2 * x) *
          (0.5 * Real.log (2 * x / (q : ℝ) ^ 2 + 4) +
            0.9 * (8 + Real.log q)) ≤
        (x / q) * Real.log (2 * x) *
          (0.5 * (Real.log (2 * x) + 15)) := by
            gcongr
      _ = 0.5 * (x / q) * Real.log (2 * x) *
          (Real.log (2 * x) + 15) := by ring
  have hexp_four : Real.exp 4 ≤ (q : ℝ) := by
    apply le_of_lt
    calc
      Real.exp 4 = Real.exp 1 ^ (4 : ℕ) := by
        rw [← Real.exp_nat_mul]
        norm_num
      _ < (3 : ℝ) ^ (4 : ℕ) := by
        exact pow_lt_pow_left₀ Real.exp_one_lt_three (Real.exp_pos 1).le
          (by norm_num)
      _ ≤ (q : ℝ) := by norm_num; linarith
  have hlogq_four : (4 : ℝ) ≤ Real.log q :=
    (Real.le_log_iff_exp_le hqpos).2 hexp_four
  have hlogprod :
      (51.6 : ℝ) ≤ Real.log q * (Real.log q + 8.9) := by
    nlinarith [sq_nonneg (Real.log (q : ℝ) - 4)]
  have hq_sq : (10000 : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith
  have hqlinear : (10000 : ℝ) * q ≤ x := by
    calc
      (10000 : ℝ) * q ≤ (q : ℝ) ^ 2 * q :=
        mul_le_mul_of_nonneg_right hq_sq hqnonneg
      _ = (q : ℝ) ^ 3 := by ring
      _ ≤ x := hqcube
  have hsqrtqpos : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.2 hqpos
  have hsqrtxnonneg : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hsqrt10000 : Real.sqrt (10000 : ℝ) = 100 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10000),
      Real.sqrt_nonneg (10000 : ℝ)]
  have hsqrt_bound : 100 * Real.sqrt (q : ℝ) ≤ Real.sqrt x := by
    calc
      100 * Real.sqrt (q : ℝ) = Real.sqrt (10000 * (q : ℝ)) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 10000)]
        rw [hsqrt10000]
      _ ≤ Real.sqrt x := Real.sqrt_le_sqrt hqlinear
  have hx_over_sqrtq :
      100 * Real.sqrt x ≤ x / Real.sqrt (q : ℝ) := by
    apply (le_div_iff₀ hsqrtqpos).2
    calc
      100 * Real.sqrt x * Real.sqrt (q : ℝ) =
          Real.sqrt x * (100 * Real.sqrt (q : ℝ)) := by ring
      _ ≤ Real.sqrt x * Real.sqrt x :=
        mul_le_mul_of_nonneg_left hsqrt_bound hsqrtxnonneg
      _ = x := Real.mul_self_sqrt hxnonneg
  have hpresecond :
      (0.301 * Real.log q ^ 2 + 2.66 * Real.log q) *
          (x / Real.sqrt q) ≤
        0.301 * (x / Real.sqrt q) * Real.log q *
          (Real.log q + 8.9) := by
    have hcoef :
        0.301 * Real.log q ^ 2 + 2.66 * Real.log q ≤
          0.301 * Real.log q * (Real.log q + 8.9) := by
      nlinarith
    calc
      (0.301 * Real.log q ^ 2 + 2.66 * Real.log q) *
          (x / Real.sqrt q) ≤
        (0.301 * Real.log q * (Real.log q + 8.9)) *
          (x / Real.sqrt q) := by gcongr
      _ = 0.301 * (x / Real.sqrt q) * Real.log q *
          (Real.log q + 8.9) := by ring
  have hsieve :
      20.16 * Real.sqrt x ≤
        0.009 * (x / Real.sqrt q) * Real.log q *
          (Real.log q + 8.9) := by
    calc
      20.16 * Real.sqrt x ≤
          0.009 * 51.6 * (100 * Real.sqrt x) := by
        nlinarith
      _ ≤ 0.009 *
          (Real.log q * (Real.log q + 8.9)) *
          (x / Real.sqrt q) := by
        gcongr
      _ = 0.009 * (x / Real.sqrt q) * Real.log q *
          (Real.log q + 8.9) := by ring
  have hsecond :
      (0.301 * Real.log q ^ 2 + 2.66 * Real.log q) *
          (x / Real.sqrt q) + 20.16 * Real.sqrt x ≤
        0.31 * (x / Real.sqrt q) * Real.log q *
          (Real.log q + 8.9) := by
    linarith [hpresecond, hsieve]
  have hsource := TaoFivePrimes.exp_sum_estimate_small_q_source_envelope
    x alpha beta a q q0 hx hq hqx haq halpha hbeta hq0 hsmall
  linarith

#print axioms solution

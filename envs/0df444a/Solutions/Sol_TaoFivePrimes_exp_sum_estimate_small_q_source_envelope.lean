-- Prove2me | solution 1 for TaoFivePrimes.exp_sum_estimate_small_q_source_envelope
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-09-12T12:47:36.363665+00:00
-- url     : https://prove2.me/submissions/d141b444-e27e-44af-bd8c-d1e1e6456cbe

import Theorems.Thm_TaoFivePrimes_small_q_modulus_two_source_envelope
import Theorems.Thm_TaoFivePrimes_small_q_modulus_transfer_source_envelope
import Mathlib.Tactic

open scoped ArithmeticFunction.vonMangoldt

theorem solution
    (x alpha beta : ℝ) (a : ℤ) (q q0 : ℕ)
    (hx : (10 : ℝ) ^ 20 ≤ x)
    (hq : 100 ≤ q) (hqx : (q : ℝ) ≤ x / 100)
    (haq : Nat.Coprime a.natAbs q)
    (halpha : 4 * alpha = (a : ℝ) / q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (hq0 : ∀ p ∈ q0.primeFactors, (p : ℝ) ≤ Real.sqrt x)
    (hsmall : (q : ℝ) ≤ x ^ (1 / 3 : ℝ)) :
    ‖TaoFivePrimes.smoothedExpSum TaoFivePrimes.eta0 q0 x alpha‖ ≤
      (x / q) * Real.log (2 * x) *
          (0.5 * Real.log (2 * x / (q : ℝ) ^ 2 + 4) +
            0.9 * (8 + Real.log q)) +
        (0.301 * Real.log q ^ 2 + 2.66 * Real.log q) *
          (x / Real.sqrt q) +
        20.16 * Real.sqrt x := by
  by_cases hz : q0 = 0
  · subst q0
    have hzero : TaoFivePrimes.smoothedExpSum TaoFivePrimes.eta0 0 x alpha = 0 := by
      unfold TaoFivePrimes.smoothedExpSum
      have hterm (n : ℕ) :
          (if Nat.Coprime n 0 then
            (Λ n : ℂ) * TaoFivePrimes.expCircle (alpha * n) *
              (TaoFivePrimes.eta0 ((n : ℝ) / x) : ℂ)
          else 0) = 0 := by
        by_cases h : n = 1
        · subst n
          simp
        · simp [Nat.coprime_zero_right, h]
      simp_rw [hterm]
      simp
    rw [hzero, norm_zero]
    have hx0 : 0 ≤ x := by linarith
    have hq1 : (1 : ℝ) ≤ q := by
      exact_mod_cast (show 1 ≤ q by omega)
    have hlq : 0 ≤ Real.log q := Real.log_nonneg hq1
    have hlx : 0 ≤ Real.log (2 * x) := Real.log_nonneg (by linarith)
    have hdiv : 0 ≤ 2 * x / (q : ℝ) ^ 2 := by positivity
    have hli : 0 ≤ Real.log (2 * x / (q : ℝ) ^ 2 + 4) :=
      Real.log_nonneg (by linarith)
    have hcore :
        0 ≤ (x / q) * Real.log (2 * x) *
              (0.5 * Real.log (2 * x / (q : ℝ) ^ 2 + 4) +
                0.9 * (8 + Real.log q)) +
            (0.301 * Real.log q ^ 2 + 2.66 * Real.log q) *
              (x / Real.sqrt q) := by
      positivity
    exact add_nonneg hcore (by positivity)
  · have hc := TaoFivePrimes.small_q_modulus_two_source_envelope
        x alpha beta a q hx hq hqx haq halpha hbeta hsmall
    have ht := TaoFivePrimes.small_q_modulus_transfer_source_envelope
        x alpha q0 hx (Nat.pos_of_ne_zero hz) hq0
    calc
      _ ≤ ‖TaoFivePrimes.smoothedExpSum TaoFivePrimes.eta0 q0 x alpha -
            TaoFivePrimes.smoothedExpSum TaoFivePrimes.eta0 2 x alpha‖ +
          ‖TaoFivePrimes.smoothedExpSum TaoFivePrimes.eta0 2 x alpha‖ := by
            simpa only [sub_add_cancel] using
              norm_add_le
                (TaoFivePrimes.smoothedExpSum TaoFivePrimes.eta0 q0 x alpha -
                  TaoFivePrimes.smoothedExpSum TaoFivePrimes.eta0 2 x alpha)
                (TaoFivePrimes.smoothedExpSum TaoFivePrimes.eta0 2 x alpha)
      _ ≤ _ := by linarith

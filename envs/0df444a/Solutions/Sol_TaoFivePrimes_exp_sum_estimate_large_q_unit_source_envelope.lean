-- Prove2me | solution 1 for TaoFivePrimes.exp_sum_estimate_large_q_unit_source_envelope
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-12T13:23:53.988197+00:00
-- url     : https://prove2.me/submissions/308e42ec-6604-4445-8b66-e021c99c18bb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib

import Definitions.Def_TaoFivePrimes_SmoothedExpSum

import Definitions.Def_TaoFivePrimes_RepresentationCount

import Theorems.Thm_TaoFivePrimes_theorem51_unit_numerator_bound

import Theorems.Thm_TaoFivePrimes_small_q_modulus_transfer_source_envelope


namespace TaoFivePrimes

/-- Specialize the three logarithmic factors in Theorem 5.1. -/
theorem large_q_log_specialization (x U V : ℝ) (hx : 0 < x) (hV : 0 < V)
    (hU : U = x / V ^ 2) :
    Real.log (x / (U * V)) = Real.log V ∧
    Real.log (V * x / U) = 3 * Real.log V ∧
    Real.log (x / U) = 2 * Real.log V := by
  have h1 : x / (U * V) = V := by rw [hU]; field_simp
  have h2 : V * x / U = V ^ 3 := by rw [hU]; field_simp
  have h3 : x / U = V ^ 2 := by rw [hU]; field_simp
  rw [h1, h2, h3, Real.log_pow, Real.log_pow]
  norm_num

end TaoFivePrimes



namespace TaoFivePrimes

theorem smoothedExpSum_zero_modulus (eta : ℝ → ℝ) (x alpha : ℝ) :
    smoothedExpSum eta 0 x alpha = 0 := by
  unfold smoothedExpSum
  calc
    _ = ∑' _ : ℕ, (0 : ℂ) := by
      apply tsum_congr
      intro n
      by_cases hn : n = 1
      · subst n
        simp
      · simp [Nat.coprime_zero_right, hn]
    _ = 0 := tsum_zero

end TaoFivePrimes


open TaoFivePrimes


theorem solution
    (x alpha beta U V : ℝ) (a : ℤ) (q q0 : ℕ)
    (hx : (10 : ℝ) ^ 20 ≤ x)
    (hq : 100 ≤ q) (hqx : (q : ℝ) ≤ x / 100)
    (haq : Nat.Coprime a.natAbs q) (haunit : a.natAbs = 1)
    (halpha : 4 * alpha = (a : ℝ) / q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (hq0 : ∀ p ∈ q0.primeFactors, (p : ℝ) ≤ Real.sqrt x)
    (hlarge : x ^ (2 / 3 : ℝ) ≤ (q : ℝ))
    (hU : U = x / V ^ 2) (hV : V = 1.02 * x / q)
    (hU40 : 40 ≤ U) (hV40 : 40 ≤ V)
    (hUx : U < x) (hVx : V < x)
    (hUV : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2)
    (hUVq : U * V < (q : ℝ) - 1) :
    ‖smoothedExpSum eta0 q0 x alpha‖ ≤
      (96 / Real.pi ^ 2) * (x / (x / q) ^ 2) *
          Real.log (4 * x) * Real.log (4 * Real.exp 1 * q / Real.pi) +
        (0.1 * (x / Real.sqrt q) +
          0.39 * (x / Real.sqrt (x / q))) * 3 * Real.log V ^ 2 +
        (0.55 * (x / Real.sqrt U) +
          0.78 * (x / Real.sqrt V)) * 2 * Real.log V +
        20.16 * Real.sqrt x := by
  have hx0 : 0 < x := by linarith
  have hV0 : 0 < V := by linarith
  by_cases hz : q0 = 0
  · subst q0
    rw [smoothedExpSum_zero_modulus, norm_zero]
    have hlogx : 0 ≤ Real.log (4 * x) := Real.log_nonneg (by linarith)
    have hlogV : 0 ≤ Real.log V := Real.log_nonneg (by linarith)
    have hqR : (100 : ℝ) ≤ q := by exact_mod_cast hq
    have he : 1 ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith
    have hprod : 1 ≤ Real.exp 1 * q := by
      nlinarith [mul_nonneg (sub_nonneg.mpr he) (show (0 : ℝ) ≤ (q : ℝ) - 1 by linarith)]
    have harg : 1 ≤ 4 * Real.exp 1 * q / Real.pi := by
      apply (le_div_iff₀ Real.pi_pos).2
      nlinarith [Real.pi_lt_four]
    have hlogq : 0 ≤ Real.log (4 * Real.exp 1 * q / Real.pi) := Real.log_nonneg harg
    positivity
  · have ht := small_q_modulus_transfer_source_envelope x alpha q0 hx
      (Nat.pos_of_ne_zero hz) hq0
    have hb := theorem51_unit_numerator_bound x alpha beta U V a q
      (by omega) haq haunit halpha hbeta hU40 hV40 hUx hVx hUV hUV2 hUVq
    obtain ⟨h1, h2, h3⟩ := large_q_log_specialization x U V hx0 hV0 hU
    rw [h1, h2, h3] at hb
    have htri := norm_add_le
      (smoothedExpSum eta0 q0 x alpha - smoothedExpSum eta0 2 x alpha)
      (smoothedExpSum eta0 2 x alpha)
    rw [sub_add_cancel] at htri
    nlinarith


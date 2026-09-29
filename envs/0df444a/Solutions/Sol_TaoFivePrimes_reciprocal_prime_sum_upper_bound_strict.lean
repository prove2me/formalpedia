-- Prove2me | solution 1 for TaoFivePrimes.reciprocal_prime_sum_upper_bound_strict
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-24T15:56:18.001215+00:00
-- url     : https://prove2.me/submissions/512a35d6-7076-4305-94d9-787188caae7f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_TaoFivePrimes_mawia_reciprocal_sum_bound
import Mathlib

/-!
# Reduction of `TaoFivePrimes.reciprocal_prime_sum_upper_bound_strict`

Target: for every real `x >= 10^8`,

    sum_{p <= x} 1/p <  log log x + gamma + sum'_p (log (1 - 1/p) + 1/p)
                          + log (1 + 1/(2 log^2 x)).

Written with `B := gamma + sum'_p (log (1 - 1/p) + 1/p)` (the Meissel-Mertens
constant, exactly as the platform node spells it) this is

    A_1(x) := sum_{p <= x} 1/p - log log x - B  <  log (1 + 1/(2 log^2 x)).

The single input is Mawia's explicit Mertens sum bound
(`TaoFivePrimes.mawia_reciprocal_sum_bound`, published as `a182289a`),

    |A_1(x)| <= 4 / log^3 x        (x >= 2),

which is far stronger than needed here; the rest is the elementary numeric fact

    4/u^3 < log (1 + 1/(2u^2))      for u >= 16,

obtained from `log (1+z) >= z/(1+z)` together with `log (10^8) >= 16`.

This replaces an earlier plan of deriving the bound from the published Chebyshev
input `|psi t - t| <= t/(40 log t)` by Abel summation, which cannot work: that
identity produces an error `1/(40 log x)`, larger than the `1/(2 log^2 x)`
allowance for every `x >= 1.0668 * 10^8`. See `missions/five-primes/A-star-route-audit.md`.
-/

noncomputable section

/-- `log (1 + z) >= z / (1 + z)` for `z > -1`, from `Real.log_le_sub_one_of_pos`
applied to `(1+z)⁻¹` and `Real.log_inv`. -/
private lemma log_one_add_ge (z : ℝ) (hz : -1 < z) :
    z / (1 + z) ≤ Real.log (1 + z) := by
  have hpos : 0 < 1 + z := by linarith
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
  rw [Real.log_inv _] at h
  have hinv : (1 + z)⁻¹ - 1 = -(z / (1 + z)) := by field_simp; ring
  rw [hinv] at h
  linarith

/-- `log 10 > 2`, hence `log (10^8) = 8 log 10 > 16`. -/
private lemma log_ten_pow_eight_gt : (16 : ℝ) < Real.log (10 ^ 8) := by
  have hexp2 : Real.exp 2 < 10 := by
    have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have h2 : 0 < Real.exp 1 := Real.exp_pos 1
    have h3 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    rw [h3]
    nlinarith
  have hlog10 : (2 : ℝ) < Real.log 10 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 10)]
    exact hexp2
  have hp : Real.log ((10 : ℝ) ^ 8) = 8 * Real.log 10 := by
    rw [Real.log_pow]
    push_cast
    ring
  rw [hp]
  linarith

theorem solution (x : ℝ) (hx : 10 ^ 8 ≤ x) :
    (∑ p ∈ Nat.primesLE ⌊x⌋₊, 1 / (p : ℝ)) <
      Real.log (Real.log x) + Real.eulerMascheroniConstant +
        (∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) +
        Real.log (1 + 1 / (2 * (Real.log x) ^ 2)) := by
  have hx2 : (2 : ℝ) ≤ x := by linarith
  have hM := TaoFivePrimes.mawia_reciprocal_sum_bound x hx2
  have hS : (∑ p ∈ Nat.primesLE ⌊x⌋₊, 1 / (p : ℝ)) ≤
      Real.log (Real.log x) + (Real.eulerMascheroniConstant +
        ∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) +
        4 / (Real.log x) ^ 3 := by
    have h := (abs_le.mp hM).2
    linarith
  have hxpos : (0 : ℝ) < x := by linarith
  have hlog10 : (0 : ℝ) < Real.log (10 ^ 8) := by linarith [log_ten_pow_eight_gt]
  have hu : (16 : ℝ) ≤ Real.log x := le_trans (le_of_lt log_ten_pow_eight_gt)
    (Real.log_le_log (by norm_num : (0 : ℝ) < 10 ^ 8) hx)
  have hu3 : (0 : ℝ) < Real.log x := by linarith
  have hnum : 4 / (Real.log x) ^ 3 < Real.log (1 + 1 / (2 * (Real.log x) ^ 2)) := by
    have hz : -1 < 1 / (2 * (Real.log x) ^ 2) := by
      have : 0 < 1 / (2 * (Real.log x) ^ 2) := by positivity
      linarith
    have hlow := log_one_add_ge (1 / (2 * (Real.log x) ^ 2)) hz
    have hden : 1 + 1 / (2 * (Real.log x) ^ 2) = (2 * (Real.log x) ^ 2 + 1) / (2 * (Real.log x) ^ 2) := by
      field_simp
    have hsimp : (1 / (2 * (Real.log x) ^ 2)) / (1 + 1 / (2 * (Real.log x) ^ 2))
        = 1 / (2 * (Real.log x) ^ 2 + 1) := by
      rw [hden]
      field_simp
    rw [hsimp] at hlow
    have hkey : 4 * (2 * (Real.log x) ^ 2 + 1) < (Real.log x) ^ 3 := by nlinarith
    have hpos2 : (0 : ℝ) < 2 * (Real.log x) ^ 2 + 1 := by positivity
    have hfrac : 4 / (Real.log x) ^ 3 < 1 / (2 * (Real.log x) ^ 2 + 1) := by
      rw [div_lt_div_iff₀ (pow_pos hu3 3) hpos2]
      simpa using hkey
    exact hfrac.trans_le hlow
  linarith

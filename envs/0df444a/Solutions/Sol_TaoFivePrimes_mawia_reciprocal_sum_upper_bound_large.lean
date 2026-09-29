-- Prove2me | solution 1 for TaoFivePrimes.mawia_reciprocal_sum_upper_bound_large
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T22:44:07.374984+00:00
-- url     : https://prove2.me/submissions/63127b03-d14a-4e49-ac3c-d69ae7a27dec
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_TaoFivePrimes_axler_theta_error_log_four
import Theorems.Thm_TaoFivePrimes_reciprocal_primes_theta_tail_identity
import Theorems.Thm_TaoFivePrimes_theta_log4_tail_bound
import Mathlib

theorem solution (x : ℝ) (hlarge : 10 ^ 8 ≤ x) :
    (∑ p ∈ Nat.primesLE ⌊x⌋₊, 1 / (p : ℝ)) ≤
      Real.log (Real.log x) +
        (Real.eulerMascheroniConstant +
          ∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) +
        4 / (Real.log x) ^ 3 := by
  have hx : 1 < x := by linarith
  have hxp : 0 < x := by linarith
  have hlog : 10 ≤ Real.log x := by
    have htwo := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at htwo
    have hmono := Real.log_le_log (show (0 : ℝ) < 2 ^ 20 by norm_num)
      (show (2 : ℝ) ^ 20 ≤ x by norm_num at hlarge ⊢; linarith)
    rw [Real.log_pow] at hmono
    norm_num at hmono
    linarith
  have hlp : 0 < Real.log x := by linarith
  let E : ℝ → ℝ := fun t => (∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ)) - t
  have hE : ∀ t, x ≤ t → |E t| ≤ 100 * t / (Real.log t) ^ 4 := by
    intro t ht
    exact (TaoFivePrimes.axler_theta_error_log_four t (by linarith)).le
  have hend : E x / (x * Real.log x) ≤ 100 / (Real.log x) ^ 5 := by
    calc
      E x / (x * Real.log x) ≤ (100 * x / (Real.log x) ^ 4) / (x * Real.log x) :=
        div_le_div_of_nonneg_right ((le_abs_self (E x)).trans (hE x le_rfl))
          (le_of_lt (mul_pos hxp hlp))
      _ = 100 / (Real.log x) ^ 5 := by field_simp [ne_of_gt hxp, ne_of_gt hlp] <;> ring
  have htail := TaoFivePrimes.theta_log4_tail_bound E x hx hE
  have htail_lower := neg_le_of_abs_le htail
  have hbudget : 100 / (Real.log x) ^ 5 +
      (25 / (Real.log x) ^ 4 + 20 / (Real.log x) ^ 5) ≤
      4 / (Real.log x) ^ 3 := by
    have hpoly : 0 ≤ 4 * (Real.log x) ^ 2 - 25 * Real.log x - 120 := by
      nlinarith [sq_nonneg (Real.log x - 10)]
    apply (le_of_sub_nonneg ?_)
    have hid : 4 / (Real.log x) ^ 3 -
        (100 / (Real.log x) ^ 5 + (25 / (Real.log x) ^ 4 + 20 / (Real.log x) ^ 5)) =
        (4 * (Real.log x) ^ 2 - 25 * Real.log x - 120) / (Real.log x) ^ 5 := by
      field_simp [ne_of_gt hlp]
      <;> ring
    rw [hid]
    exact div_nonneg hpoly (le_of_lt (pow_pos hlp 5))
  have hid := TaoFivePrimes.reciprocal_primes_theta_tail_identity x (by linarith)
  change (∑ p ∈ Nat.primesLE ⌊x⌋₊, 1 / (p : ℝ)) = _ + E x / (x * Real.log x) -
    (∫ t in Set.Ioi x, E t * (Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)) at hid
  linarith

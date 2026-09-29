-- Prove2me | solution 2 for TaoFivePrimes.mawia_reciprocal_sum_upper_bound_large
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T23:42:26.633671+00:00
-- url     : https://prove2.me/submissions/f9da6edb-3c0d-4604-b565-514c12658d51
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_TaoFivePrimes_dusart_theta_error_log_four
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
  have hlog : 16 ≤ Real.log x := by
    have htwo := Real.log_two_gt_d9.le
    have hmono := Real.log_le_log (show (0 : ℝ) < 2 ^ 24 by norm_num)
      (show (2 : ℝ) ^ 24 ≤ x by norm_num at hlarge ⊢; linarith)
    rw [Real.log_pow] at hmono
    norm_num at hmono
    linarith
  have hlp : 0 < Real.log x := by linarith
  let E : ℝ → ℝ := fun t => (∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ)) - t
  have hE : ∀ t, x ≤ t → |E t| ≤ 160 * t / (Real.log t) ^ 4 := by
    intro t ht
    have hs := TaoFivePrimes.dusart_theta_error_log_four t (by linarith)
    have htp : 0 ≤ t := by linarith
    have hp : 0 ≤ t / (Real.log t)^4 := by positivity
    have hb : (1513 / 10 : ℝ) * t / (Real.log t)^4 ≤ 160 * t / (Real.log t)^4 :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by norm_num : (1513 / 10 : ℝ) ≤ 160) htp)
        (by positivity)
    exact hs.trans hb
  have hend : E x / (x * Real.log x) ≤ 160 / (Real.log x) ^ 5 := by
    calc
      E x / (x * Real.log x) ≤ (160 * x / (Real.log x) ^ 4) / (x * Real.log x) :=
        div_le_div_of_nonneg_right ((le_abs_self (E x)).trans (hE x le_rfl))
          (le_of_lt (mul_pos hxp hlp))
      _ = 160 / (Real.log x) ^ 5 := by field_simp [ne_of_gt hxp, ne_of_gt hlp] <;> ring
  let F : ℝ → ℝ := fun t => (5 / 8 : ℝ) * E t
  have hF : ∀ t, x ≤ t → |F t| ≤ 100 * t / (Real.log t)^4 := by
    intro t ht
    have hf : |F t| = (5 / 8 : ℝ) * |E t| := by dsimp [F]; rw [abs_mul]; norm_num
    rw [hf]
    calc
      (5 / 8 : ℝ) * |E t| ≤ (5 / 8 : ℝ) * (160 * t / (Real.log t)^4) :=
        mul_le_mul_of_nonneg_left (hE t ht) (by norm_num)
      _ = 100 * t / (Real.log t)^4 := by ring
  have htF := TaoFivePrimes.theta_log4_tail_bound F x hx hF
  have hscale : (∫ t in Set.Ioi x, F t * (Real.log t + 1) / (t ^ 2 * (Real.log t)^2)) =
      (5 / 8 : ℝ) * ∫ t in Set.Ioi x, E t * (Real.log t + 1) / (t ^ 2 * (Real.log t)^2) := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp [F]
    ring
  rw [hscale, abs_mul] at htF
  norm_num at htF
  have htail : |∫ t in Set.Ioi x, E t * (Real.log t + 1) / (t ^ 2 * (Real.log t)^2)| ≤
      40 / (Real.log x)^4 + 32 / (Real.log x)^5 := by
    calc
      _ = (8 / 5 : ℝ) * ((5 / 8 : ℝ) * |∫ t in Set.Ioi x,
        E t * (Real.log t + 1) / (t ^ 2 * (Real.log t)^2)|) := by ring
      _ ≤ (8 / 5 : ℝ) * (25 / (Real.log x)^4 + 20 / (Real.log x)^5) :=
        mul_le_mul_of_nonneg_left htF (by norm_num)
      _ = _ := by ring
  have htail_lower := neg_le_of_abs_le htail
  have hbudget : 160 / (Real.log x) ^ 5 +
      (40 / (Real.log x) ^ 4 + 32 / (Real.log x) ^ 5) ≤
      4 / (Real.log x) ^ 3 := by
    have hpoly : 0 ≤ 4 * (Real.log x) ^ 2 - 40 * Real.log x - 192 := by
      nlinarith [sq_nonneg (Real.log x - 16)]
    apply (le_of_sub_nonneg ?_)
    have hid : 4 / (Real.log x) ^ 3 -
        (160 / (Real.log x) ^ 5 + (40 / (Real.log x) ^ 4 + 32 / (Real.log x) ^ 5)) =
        (4 * (Real.log x) ^ 2 - 40 * Real.log x - 192) / (Real.log x) ^ 5 := by
      field_simp [ne_of_gt hlp]
      <;> ring
    rw [hid]
    exact div_nonneg hpoly (le_of_lt (pow_pos hlp 5))
  have hid := TaoFivePrimes.reciprocal_primes_theta_tail_identity x (by linarith)
  change (∑ p ∈ Nat.primesLE ⌊x⌋₊, 1 / (p : ℝ)) = _ + E x / (x * Real.log x) -
    (∫ t in Set.Ioi x, E t * (Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)) at hid
  linarith

-- Prove2me | solution 1 for RvsCert.input_length
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-13T10:04:26.453875+00:00
-- url     : https://prove2.me/submissions/7fa8d653-b1c2-421c-87ac-0621036d41d5

import Mathlib
import Definitions.Def_RvsCert_Idx

open RvsCert

theorem solution :
    (∀ n : ℕ, Fintype.card (Idx n) =
      n * (2 * n - 1) * n * wX n + 2 * n ^ 2 * (2 * n - 1) * wY n) ∧
    ∃ A : ℝ, ∀ n : ℕ, 0 < n →
      (Fintype.card (Idx n) : ℝ) ≤ A * (n : ℝ) ^ 3 * (Real.logb 2 n + 1) := by
  have count (n : ℕ) : Fintype.card (Idx n) =
      n * (2 * n - 1) * n * wX n + 2 * n ^ 2 * (2 * n - 1) * wY n := by
    have races : Fintype.card (Race n) = n * (2 * n - 1) := by
      unfold Race
      rw [Fintype.card_subtype, Fintype.card_product_filter_lt, Fintype.card_fin,
        Nat.choose_two_right, Nat.mul_assoc, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
    simp only [Idx, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, races]
    ring
  refine ⟨count, 8, ?_⟩
  intro n hn
  have widthX : (wX n : ℝ) ≤ 2 * (Real.logb 2 n + 1) := by
    have hbits : wX n ≤ Nat.log 2 (2 * n ^ 2) + 1 :=
      Nat.clog_le_of_le_pow (Nat.lt_pow_succ_log_self (by decide : 1 < 2) (2 * n ^ 2))
    have hbitsR : (wX n : ℝ) ≤ (Nat.log 2 (2 * n ^ 2) : ℝ) + 1 := by
      exact_mod_cast hbits
    have hlog := Real.natLog_le_logb (2 * n ^ 2) 2
    push_cast at hlog
    rw [Real.logb_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : (n : ℝ) ^ 2 ≠ 0),
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), Real.logb_pow] at hlog
    push_cast at hlog
    linarith only [hbitsR, hlog]
  have widthY : (wY n : ℝ) ≤ Real.logb 2 n + 1 := by
    simpa [wY] using add_le_add_right (Real.natLog_le_logb n 2) 1
  have total : Fintype.card (Idx n) ≤ 2 * n ^ 3 * wX n + 4 * n ^ 3 * wY n := by
    rw [count]
    calc
      _ ≤ n * (2 * n) * n * wX n + 2 * n ^ 2 * (2 * n) * wY n := by
        gcongr <;> omega
      _ = _ := by ring
  calc
    (Fintype.card (Idx n) : ℝ) ≤ 2 * (n : ℝ) ^ 3 * wX n + 4 * (n : ℝ) ^ 3 * wY n := by
      exact_mod_cast total
    _ ≤ 2 * (n : ℝ) ^ 3 * (2 * (Real.logb 2 n + 1)) +
        4 * (n : ℝ) ^ 3 * (Real.logb 2 n + 1) :=
      add_le_add (mul_le_mul_of_nonneg_left widthX (by positivity))
        (mul_le_mul_of_nonneg_left widthY (by positivity))
    _ = _ := by ring

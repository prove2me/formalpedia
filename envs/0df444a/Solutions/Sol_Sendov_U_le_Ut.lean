-- Prove2me | solution 1 for Sendov.U_le_Ut
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:01:18.060021+00:00
-- url     : https://prove2.me/submissions/0b0482fa-ec90-4a54-af29-ae618e5e5787

import Definitions.Def_Sendov_LargeDegree_Tail
import Definitions.Def_Sendov_LargeDegree_Monotone
import Theorems.Thm_Sendov_U_eq
import Theorems.Thm_Sendov_T1_le
import Theorems.Thm_Sendov_T2_le
import Theorems.Thm_Sendov_c_ge_of_large
import Theorems.Thm_Sendov_three_add_pos


set_option autoImplicit false
open Sendov
variable {n : ℕ} {α : ℝ}
namespace Sendov
theorem _root_.solution (hn : 101 ≤ n) (hα : 0 ≤ α) (hα' : α ≤ 17) : U n α ≤ Ut α := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have hnR : (101 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hM : (100 : ℝ) ≤ M n := by simp only [M]; linarith
  have hcpos : (0 : ℝ) < c n α := by
    have := c_ge_of_large hn hα hα'
    linarith
  rw [U_eq (by omega) hα (ne_of_gt hcpos), Ut]
  have e1 : 1 / (2 * M n) ≤ 1 / 200 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have e2 : 1 / (4 * M n * (3 + α)) ≤ 1 / (400 * (3 + α)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have e3 := T1_le hn hα hα'
  have hB : (0 : ℝ) ≤ α / (3 + α) := div_nonneg hα (by linarith)
  have hb0 : (0 : ℝ) ≤ Real.sqrt (α / (3 + α)) := Real.sqrt_nonneg _
  have hb1 : Real.sqrt (α / (3 + α)) ≤ 1 := by
    have hle : α / (3 + α) ≤ 1 := by rw [div_le_one h3]; linarith
    calc Real.sqrt (α / (3 + α)) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hle
      _ = 1 := Real.sqrt_one
  have hpow : Real.sqrt (α / (3 + α)) ^ (101 - 4) ≤ (α / (3 + α)) ^ 48 := by
    have h97 : Real.sqrt (α / (3 + α)) ^ (101 - 4)
        = (α / (3 + α)) ^ 48 * Real.sqrt (α / (3 + α)) := by
      rw [show (101 : ℕ) - 4 = 2 * 48 + 1 by norm_num, pow_succ, pow_mul, Real.sq_sqrt hB]
    rw [h97]
    nlinarith [pow_nonneg hB 48]
  have e4 : T2 101 α
      ≤ (100 - 2 * α) ^ 2 / 100 * 101 * 99 / (16 * (3 + α)) * (α / (3 + α)) ^ 48 := by
    have hA101 : A 101 α = (100 - 2 * α) / 100 := by
      simp only [A, M]
      norm_num
      ring
    have hT2 : T2 101 α = (100 - 2 * α) ^ 2 / 100 * 101 * 99 / (16 * (3 + α))
        * Real.sqrt (α / (3 + α)) ^ (101 - 4) := by
      simp only [T2, hA101, M]
      norm_num
      ring_nf
      tauto
    rw [hT2]
    exact mul_le_mul_of_nonneg_left hpow (by positivity)
  have e5 := (T2_le hn hα hα').trans e4
  linarith
end Sendov

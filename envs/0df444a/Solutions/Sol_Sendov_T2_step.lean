-- Prove2me | solution 1 for Sendov.T2_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:59:51.408847+00:00
-- url     : https://prove2.me/submissions/9b9a26aa-7f78-44df-b3bb-d09c5c022a0b

import Definitions.Def_Sendov_LargeDegree_Tail
import Definitions.Def_Sendov_LargeDegree_Monotone
import Theorems.Thm_Sendov_tail2_poly
import Theorems.Thm_Sendov_sqrtB_le
import Theorems.Thm_Sendov_three_add_pos


set_option autoImplicit false
open Sendov
variable {n : ℕ} {α : ℝ}
namespace Sendov
theorem _root_.solution (hn : 101 ≤ n) (hα : 0 ≤ α) (hα' : α ≤ 17) : T2 (n + 1) α ≤ T2 n α := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have hnR : (101 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hb0 : (0 : ℝ) ≤ Real.sqrt (α / (3 + α)) := Real.sqrt_nonneg _
  have hb1 : Real.sqrt (α / (3 + α)) ≤ 12 / 13 := sqrtB_le hα hα'
  have hA1 : A (n + 1) α = ((n : ℝ) - 2 * α) / (n : ℝ) := by
    simp only [A, M]
    push_cast
    rw [show ((n : ℝ) + 1 - 1) = (n : ℝ) from by ring]
    field_simp
  have hA2 : A n α = ((n : ℝ) - 1 - 2 * α) / ((n : ℝ) - 1) := by
    simp only [A, M]
    field_simp
  have hk : (0 : ℝ) ≤ (n : ℝ) - 101 := by linarith
  have hcert := tail2_poly (k := (n : ℝ) - 101) hk hα hα'
  have hCn1 : (0 : ℝ) ≤ A (n + 1) α ^ 2 * ((n + 1 : ℕ) : ℝ) * M (n + 1)
      * (((n + 1 : ℕ) : ℝ) - 2) / (16 * (3 + α)) := by
    have hM : (0 : ℝ) ≤ M (n + 1) := by simp only [M]; push_cast; linarith
    have h2 : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) - 2 := by push_cast; linarith
    have h1 : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by positivity
    positivity
  -- the coefficient inequality
  have hstep : A (n + 1) α ^ 2 * ((n + 1 : ℕ) : ℝ) * M (n + 1) * (((n + 1 : ℕ) : ℝ) - 2)
        / (16 * (3 + α)) * Real.sqrt (α / (3 + α))
      ≤ A n α ^ 2 * (n : ℝ) * M n * ((n : ℝ) - 2) / (16 * (3 + α)) := by
    refine le_trans (mul_le_mul_of_nonneg_left hb1 hCn1) ?_
    rw [← sub_nonneg]
    have key : A n α ^ 2 * (n : ℝ) * M n * ((n : ℝ) - 2) / (16 * (3 + α))
          - A (n + 1) α ^ 2 * ((n + 1 : ℕ) : ℝ) * M (n + 1) * (((n + 1 : ℕ) : ℝ) - 2)
              / (16 * (3 + α)) * (12 / 13)
        = (13 * ((n : ℝ) - 1 - 2 * α) ^ 2 * ((n : ℝ) - 2) * (n : ℝ) ^ 2
            - 12 * ((n : ℝ) - 2 * α) ^ 2 * ((n : ℝ) + 1) * ((n : ℝ) - 1) ^ 2)
          / (208 * (3 + α) * (n : ℝ) * ((n : ℝ) - 1)) := by
      simp only [hA1, hA2, M]
      push_cast
      field_simp
      ring
    rw [key]
    refine div_nonneg ?_ (by positivity)
    nlinarith [hcert]
  have hexp : n + 1 - 4 = (n - 4) + 1 := by omega
  calc T2 (n + 1) α
      = A (n + 1) α ^ 2 * ((n + 1 : ℕ) : ℝ) * M (n + 1) * (((n + 1 : ℕ) : ℝ) - 2)
            / (16 * (3 + α)) * Real.sqrt (α / (3 + α))
          * Real.sqrt (α / (3 + α)) ^ (n - 4) := by
        rw [T2, hexp, pow_succ]
        ring
    _ ≤ A n α ^ 2 * (n : ℝ) * M n * ((n : ℝ) - 2) / (16 * (3 + α))
          * Real.sqrt (α / (3 + α)) ^ (n - 4) :=
        mul_le_mul_of_nonneg_right hstep (pow_nonneg hb0 _)
    _ = T2 n α := by rw [T2]
end Sendov

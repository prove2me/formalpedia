-- Prove2me | solution 1 for Sendov.beta_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:01:29.899809+00:00
-- url     : https://prove2.me/submissions/bf107b05-fb2d-4ec6-8126-c80c5534fb8a

import Definitions.Def_Sendov_Reduction_Stat
import Definitions.Def_Sendov_Reduction_Simplified
import Theorems.Thm_Sendov_rpow_add_le_of_one_le
import Theorems.Thm_Sendov_one_sub_mul_pos
import Theorems.Thm_Sendov_QQ_eq


set_option autoImplicit false
open Sendov
open MeasureTheory
variable {n : ℕ} {a x t α : ℝ}
namespace Sendov
theorem _root_.solution (hn : 5 ≤ n) (ha : 0 < a) (ha1 : a < 1) (hx : x ^ 2 ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2)
      ≤ (1 - a * x * t) ^ ((n : ℝ) - 2)
        + ((n : ℝ) - 2) / 2 * (a ^ 2 * t ^ 2 * (1 - x ^ 2))
          * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 4) / 2) := by
  have hnR : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hy : (0 : ℝ) < 1 - a * x * t := one_sub_mul_pos ha ha1 hx ht0 ht1
  have hP : (0 : ℝ) ≤ (1 - a * x * t) ^ 2 := sq_nonneg _
  have hQ : (0 : ℝ) ≤ a ^ 2 * t ^ 2 * (1 - x ^ 2) := by
    have : (0 : ℝ) ≤ 1 - x ^ 2 := by linarith
    positivity
  have hsum : QQ (a * x) (a ^ 2) t
      = (1 - a * x * t) ^ 2 + a ^ 2 * t ^ 2 * (1 - x ^ 2) := by
    rw [QQ_eq]; ring
  have hPQ : (0 : ℝ) < (1 - a * x * t) ^ 2 + a ^ 2 * t ^ 2 * (1 - x ^ 2) := by positivity
  have hp : (1 : ℝ) ≤ ((n : ℝ) - 2) / 2 := by linarith
  have hb := rpow_add_le_of_one_le hP hPQ hp
  rw [← hsum] at hb
  -- `((1-axt)²)^((n-2)/2) = (1-axt)^(n-2)`
  have hchord : ((1 - a * x * t) ^ 2 : ℝ) ^ (((n : ℝ) - 2) / 2)
      = (1 - a * x * t) ^ ((n : ℝ) - 2) := by
    rw [← Real.rpow_natCast (1 - a * x * t) 2, ← Real.rpow_mul hy.le]
    congr 1
    push_cast
    ring
  -- `(n-2)/2 - 1 = (n-4)/2`
  have hexp : ((n : ℝ) - 2) / 2 - 1 = ((n : ℝ) - 4) / 2 := by ring
  rw [hchord, hexp] at hb
  exact hb
end Sendov

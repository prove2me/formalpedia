-- Prove2me | solution 1 for Sendov.R_le_of_integral_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:56:14.234673+00:00
-- url     : https://prove2.me/submissions/5c1d70b8-9928-44f7-b386-d06c211474f4

import Definitions.Def_Sendov_Defs
import Definitions.Def_Sendov_Common_Basic
import Theorems.Thm_Sendov_M_pos
import Theorems.Thm_Sendov_three_add_pos

set_option autoImplicit false
open Sendov
variable {n : ℕ} {α t : ℝ}
namespace Sendov
theorem _root_.solution (hn : 2 ≤ n) (hα : 0 ≤ α) {J : ℝ}
    (hJ : (∫ t in (0 : ℝ)..1, t ^ 3 * Q n α t ^ (((n : ℝ) - 4) / 2)) ≤ J) :
    R n α ≤ 1 / 6 + 1 / (4 * (3 + α)) + 1 / (2 * M n) + 1 / (4 * M n * (3 + α)) +
      A n α ^ 2 * n * M n * ((n : ℝ) - 2) / (4 * (3 + α)) * J := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have hn2 : (0 : ℝ) ≤ (n : ℝ) - 2 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hcoef : 0 ≤ A n α ^ 2 * n * M n * ((n : ℝ) - 2) / (4 * (3 + α)) :=
    div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg n))
      (M_pos hn).le) hn2) (by linarith)
  rw [R]
  have := mul_le_mul_of_nonneg_left hJ hcoef
  linarith
end Sendov

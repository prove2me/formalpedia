-- Prove2me | solution 1 for Sendov.U_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:59:46.086552+00:00
-- url     : https://prove2.me/submissions/c9fddf5c-6527-4caa-9229-2bfa41bbb81d

import Definitions.Def_Sendov_LargeDegree_Tail
import Definitions.Def_Sendov_LargeDegree_Monotone
import Theorems.Thm_Sendov_rpow_B_eq
import Theorems.Thm_Sendov_beta_prod
import Theorems.Thm_Sendov_three_add_pos


set_option autoImplicit false
open Sendov
variable {n : ℕ} {α : ℝ}
namespace Sendov
theorem _root_.solution (hn : 5 ≤ n) (hα : 0 ≤ α) (hc : c n α ≠ 0) :
    U n α = 1 / 6 + 1 / (4 * (3 + α)) + 1 / (2 * M n) + 1 / (4 * M n * (3 + α))
      + T1 n α + T2 n α := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have hnR : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have h2 : (n : ℝ) - 2 ≠ 0 := by linarith
  have h0 : (n : ℝ) ≠ 0 := by linarith
  have hp2 : (n : ℝ) + 2 ≠ 0 := by linarith
  have hp4 : (n : ℝ) + 4 ≠ 0 := by linarith
  simp only [U, beta_prod, T1, T2, M, A, rpow_B_eq (show 4 ≤ n by omega) hα]
  field_simp
  ring
end Sendov

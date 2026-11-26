-- Prove2me | solution 1 for Sendov.c_pos_of_le_half_M
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:44:41.47521+00:00
-- url     : https://prove2.me/submissions/392e1b7d-c2e3-4b58-8e3d-b2ae35de37f7

import Definitions.Def_Sendov_Defs
import Definitions.Def_Sendov_Common_Basic
import Theorems.Thm_Sendov_M_pos
import Theorems.Thm_Sendov_three_add_pos

set_option autoImplicit false
open Sendov
variable {n : ℕ} {α t : ℝ}
namespace Sendov
theorem _root_.solution (hn : 2 ≤ n) (hα : 0 ≤ α) (hhalf : α ≤ M n / 2) : 0 < c n α := by
  have hM : 0 < M n := M_pos hn
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have h1 : α / M n ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hM (by norm_num)]
    linarith
  have h2 : α / (2 * (3 + α)) < 1 / 2 := by
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    linarith
  simp only [c]
  linarith
end Sendov

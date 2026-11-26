-- Prove2me | solution 1 for Sendov.Q_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:56:10.697923+00:00
-- url     : https://prove2.me/submissions/81a14260-3c32-4750-b0f7-6ba1bdbf8eca

import Definitions.Def_Sendov_Defs
import Definitions.Def_Sendov_Common_Basic
import Theorems.Thm_Sendov_M_pos
import Theorems.Thm_Sendov_three_add_pos

set_option autoImplicit false
open Sendov
variable {n : ℕ} {α t : ℝ}
namespace Sendov
theorem _root_.solution (hn : 2 ≤ n) (hα : 0 ≤ α) : Q n α 1 = α / (3 + α) := by
  have hM : M n ≠ 0 := (M_pos hn).ne'
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  simp only [Q, c, A]
  field_simp
  ring
end Sendov

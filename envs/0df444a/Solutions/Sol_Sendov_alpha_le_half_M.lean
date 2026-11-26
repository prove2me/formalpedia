-- Prove2me | solution 1 for Sendov.alpha_le_half_M
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:56:25.347846+00:00
-- url     : https://prove2.me/submissions/9486b262-9c72-48ef-8639-d03d55273d8c

import Definitions.Def_Sendov_Defs
import Definitions.Def_Sendov_Common_Basic
import Theorems.Thm_Sendov_M_pos
import Theorems.Thm_Sendov_A_nonneg

set_option autoImplicit false
open Sendov
variable {n : ℕ} {α t : ℝ}
namespace Sendov
theorem _root_.solution (hn : 2 ≤ n) (hfeas : c n α ^ 2 ≤ A n α) : α ≤ M n / 2 := by
  have hM : 0 < M n := M_pos hn
  have hA : 0 ≤ A n α := A_nonneg hfeas
  rw [A] at hA
  have h : 2 * α / M n ≤ 1 := by linarith
  rw [div_le_one hM] at h
  linarith
end Sendov

-- Prove2me | solution 1 for Sendov.large_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:14:59.304862+00:00
-- url     : https://prove2.me/submissions/0656aeb4-d303-4d74-b3cb-f1546ea825d4

import Definitions.Def_Sendov_LargeDegree_Monotone
import Definitions.Def_Sendov_LargeDegree_Endgame
import Theorems.Thm_Sendov_Ut_lt_one
import Theorems.Thm_Sendov_R_le_U
import Theorems.Thm_Sendov_U_le_Ut
import Theorems.Thm_Sendov_c_ge_of_large


set_option autoImplicit false
open Sendov
variable {α : ℝ}
namespace Sendov
theorem _root_.solution {n : ℕ} (hn : 101 ≤ n) (hα : 0 ≤ α) (hα' : α ≤ 17)
    (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by
  have hcpos : (0 : ℝ) < c n α := by
    have := c_ge_of_large hn hα hα'
    linarith
  exact lt_of_le_of_lt
    (le_trans (R_le_U (by omega) hα hfeas hcpos) (U_le_Ut hn hα hα'))
    (Ut_lt_one hα hα')
end Sendov

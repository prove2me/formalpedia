-- Prove2me | solution 1 for ShiQMAConstructiveSchedule.error_rounds
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-10-01T13:05:06.395105+00:00
-- url     : https://prove2.me/submissions/c582aaa3-ef97-4019-918e-b590a7467592

import Definitions.Def_ShiQMAConstructiveSchedule
import Theorems.Thm_ShiQMAErrorIteration_dyadic_error_bound
import Theorems.Thm_ShiQMAConstructiveSchedule_eval_le_pow_budget

set_option autoImplicit false
set_option maxHeartbeats 2000000

open ShiQMAConstructiveSchedule ShiQMAErrorIteration

theorem solution (p : Polynomial ℕ) (n : ℕ) :
    error (rounds p n) ≤ ((1 : ℝ) / 2) ^ (p.eval n) := by
  have h := dyadic_error_bound (exponentBudget p n)
  have hp := pow_le_pow_of_le_one
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 : ℝ) / 2 ≤ 1)
    (eval_le_pow_budget p n)
  exact h.trans hp

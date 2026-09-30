-- Prove2me | solution 1 for ShiQMAErrorIteration.error_roundsFor
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-30T06:42:48.813056+00:00
-- url     : https://prove2.me/submissions/228002a3-7db0-4506-b0c0-2127274fe838

import Definitions.Def_ShiQMAErrorIteration
import Theorems.Thm_ShiQMAErrorIteration_dyadic_error_bound

set_option autoImplicit false
open ShiQMAErrorIteration

theorem solution (m : Nat) : error (roundsFor m) ≤ ((1 : ℝ) / 2) ^ m := by
  have h := dyadic_error_bound (Nat.log 2 m + 1)
  have hm : m ≤ 2 ^ (Nat.log 2 m + 1) :=
    Nat.le_of_lt (Nat.lt_pow_succ_log_self (by decide : 1 < 2) m)
  have hp := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 : ℝ) / 2 ≤ 1) hm
  exact (show error (roundsFor m) ≤ ((1 : ℝ) / 2) ^ (2 ^ (Nat.log 2 m + 1)) from h).trans hp

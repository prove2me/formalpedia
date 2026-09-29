-- Prove2me | solution 1 for SpinStatistics.composite_spin_parity
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T11:01:42.850037+00:00
-- url     : https://prove2.me/submissions/17689d70-d909-4f64-acc6-5ecd913dee9f

import Mathlib
import Definitions.Def_SpinStatistics_Defs

set_option autoImplicit false

open SpinStatistics in
theorem solution (l : List ℕ) (J : ℕ) (h : CanAddTo l J) :
    J % 2 = (l.countP (fun a => a % 2 = 1)) % 2 := by
  induction h with
  | nil => simp
  | @cons a b J l _ _ _ _ hpar ih =>
    rw [List.countP_cons]
    by_cases ha : a % 2 = 1
    · simp only [ha, decide_true, if_true]
      omega
    · simp only [ha, decide_false]
      simp only [Bool.false_eq_true, if_false, add_zero]
      omega

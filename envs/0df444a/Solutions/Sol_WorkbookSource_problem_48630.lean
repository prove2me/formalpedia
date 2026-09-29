-- Prove2me | solution 1 for WorkbookSource.problem_48630
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:12:42.843365+00:00
-- url     : https://prove2.me/submissions/7115cbe9-8de1-4fc1-bfb4-07af43705ec9

/- InternLM Lean-Workbook, lean_workbook_48630, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution : 5^99346 > 3^62336  := by
  calc
    (3 : ℕ)^62336 ≤ 5^62336 := pow_le_pow_left₀ (show (0 : ℕ) ≤ 3 by omega) (show (3 : ℕ) ≤ 5 by omega) _
    _ < 5^99346 := pow_lt_pow_right₀ (by norm_num) (by omega)

example : (5^99346 > 3^62336) := @solution
#print axioms solution

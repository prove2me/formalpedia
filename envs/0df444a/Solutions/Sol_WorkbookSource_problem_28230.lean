-- Prove2me | solution 1 for WorkbookSource.problem_28230
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:57:16.21566+00:00
-- url     : https://prove2.me/submissions/57bc44d8-d346-4124-81b8-a45d98d121c3

/- InternLM Lean-Workbook, lean_workbook_28230, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution : (1684 : ℚ) / 405 > 13845 / 3344  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | norm_num [Nat.cast_add]
  | solve
    | norm_num [div_lt_div_iff]
  | solve
    | norm_num [div_lt_div_left]
  | solve
    | simp [div_lt_div_iff]
      norm_num
example : ((1684 : ℚ) / 405 > 13845 / 3344) := @solution
#print axioms solution

-- Prove2me | solution 1 for WorkbookSource.problem_10832
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:50:20.950204+00:00
-- url     : https://prove2.me/submissions/9fc6e3e3-146e-4fc9-a21a-ff72d51bc410

/- InternLM Lean-Workbook, lean_workbook_10832, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution : 10! % 13 = 6  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | calc 10! % 13
  | solve
    | simp [factorial]
  | solve
    | exact_mod_cast rfl
  | solve
    | norm_num [factorial]
example : (10! % 13 = 6) := @solution
#print axioms solution

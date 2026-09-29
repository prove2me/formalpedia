-- Prove2me | solution 1 for WorkbookSource.problem_33411
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:05:55.962898+00:00
-- url     : https://prove2.me/submissions/a0adba84-445e-4343-8850-805fb227f281

/- InternLM Lean-Workbook, lean_workbook_33411, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution : (101^50) > (100^50 + 99^50)  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | simp [add_comm]
  | solve
    | clear t1
      norm_num
  | solve
    | norm_num [pow_succ]
  | solve
    | norm_num [Nat.ModEq]
example : ((101^50) > (100^50 + 99^50)) := @solution
#print axioms solution

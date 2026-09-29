-- Prove2me | solution 1 for WorkbookSource.problem_1481
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:41:00.114247+00:00
-- url     : https://prove2.me/submissions/23a40b33-8da7-4f7f-8f47-23147470db1b

/- InternLM Lean-Workbook, lean_workbook_1481, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (x : ℚ) (hx : x = 23/4) : x = 5.75  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | rw [hx]
      ring_nf
  | solve
    | rw [hx]
      norm_num [hx]
  | solve
    | linear_combination hx
  | solve
    | simp only [hx]
      norm_num [hx]
example : (∀ (x : ℚ) (hx : x = 23/4), x = 5.75) := @solution
#print axioms solution

-- Prove2me | solution 1 for WorkbookSource.problem_25121
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:53:36.187934+00:00
-- url     : https://prove2.me/submissions/34c7274a-fd6f-4535-a582-ec10be4f7ba6

/- InternLM Lean-Workbook, lean_workbook_25121, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution :
  1023 = (2^5 - 1) * (2^5 + 1)  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | congr 1
  | solve
    | simp [pow_succ]
  | solve
    | simp [add_comm]
  | solve
    | norm_num [Nat.gcd]
example : (1023 = (2^5 - 1) * (2^5 + 1)) := @solution
#print axioms solution

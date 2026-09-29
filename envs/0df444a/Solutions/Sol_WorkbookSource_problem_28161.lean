-- Prove2me | solution 1 for WorkbookSource.problem_28161
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:57:15.529209+00:00
-- url     : https://prove2.me/submissions/45ed651a-cd8b-4500-b4e4-142cfd90272f

/- InternLM Lean-Workbook, lean_workbook_28161, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution :
  7! / (3! * 3!) = 140  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | congr 1
  | solve
    | simp [Nat.factorial]
  | solve
    | norm_num [Nat.factorial]
  | solve
    | simp [Nat.factorial_succ]
example : (7! / (3! * 3!) = 140) := @solution
#print axioms solution

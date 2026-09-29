-- Prove2me | solution 1 for WorkbookSource.problem_50698
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:09:57.770981+00:00
-- url     : https://prove2.me/submissions/4634ab71-911c-46dc-9a9d-93e52d840359

/- InternLM Lean-Workbook, lean_workbook_50698, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution :
  Nat.factorial 4 / (Nat.factorial 2 * Nat.factorial 2) = 6  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | congr 2
  | solve
    | rw [factorial]
      rfl
  | solve
    | norm_num [factorial]
  | solve
    | simp [Nat.factorial]
example : (Nat.factorial 4 / (Nat.factorial 2 * Nat.factorial 2) = 6) := @solution
#print axioms solution

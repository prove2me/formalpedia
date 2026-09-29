-- Prove2me | solution 1 for WorkbookSource.problem_9982
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:50:18.569555+00:00
-- url     : https://prove2.me/submissions/f9c5aff3-29b6-45e9-8250-36c6acbe3e67

/- InternLM Lean-Workbook, lean_workbook_9982, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (f : ℝ → ℝ) (x : ℝ) (f_def : f = fun x => x^2 + x) : f 1 = 2  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | rw [f_def]
      norm_num
  | solve
    | rw [f_def]
      norm_num at *
  | solve
    | simp [f_def, sq]
      norm_num
  | solve
    | simp [f_def]
      linarith [f_def]
  | solve
    | simp [f_def]
      nlinarith [f_def]
example : (∀ (f : ℝ → ℝ) (x : ℝ) (f_def : f = fun x => x^2 + x), f 1 = 2) := @solution
#print axioms solution

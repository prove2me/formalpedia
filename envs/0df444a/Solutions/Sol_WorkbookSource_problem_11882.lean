-- Prove2me | solution 1 for WorkbookSource.problem_11882
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:50:25.998688+00:00
-- url     : https://prove2.me/submissions/e691c265-e922-4ce4-8f8a-4d36cf1ed909

/- InternLM Lean-Workbook, lean_workbook_11882, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (a b c : ℝ) (hab : 1 < a) (hbc : 1 < b) (hca : 1 < c) : a * b + b * c + c * a > 3  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | repeat' nlinarith
  | solve
    | nlinarith [mul_assoc a b c]
  | solve
    | simp only [mul_comm]
      nlinarith
  | solve
    | repeat nlinarith [hab, hbc, hca]
example : (∀ (a b c : ℝ) (hab : 1 < a) (hbc : 1 < b) (hca : 1 < c), a * b + b * c + c * a > 3) := @solution
#print axioms solution

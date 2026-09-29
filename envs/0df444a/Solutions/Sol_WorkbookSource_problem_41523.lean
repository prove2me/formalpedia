-- Prove2me | solution 1 for WorkbookSource.problem_41523
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:17:53.508426+00:00
-- url     : https://prove2.me/submissions/e968e295-9f54-4c31-8bc4-2f21bc6157de

/- InternLM Lean-Workbook, lean_workbook_41523, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution : ∀ a b c : ℝ, 2 * (a + b + c)^3 + 9 * a * b * c - 7 * (a + b + c) * (a * b + b * c + c * a) = (a - b)^2 * (a + b) + (b - c)^2 * (b + c) + (c - a)^2 * (c + a)  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | intros a b c
      ring
  | solve
    | intros
      simp [sq]
      ring
  | solve
    | repeat' intro a b c; ring
  | solve
    | simp [sq]
      intro a b c
      ring
example : (∀ a b c : ℝ, 2 * (a + b + c)^3 + 9 * a * b * c - 7 * (a + b + c) * (a * b + b * c + c * a) = (a - b)^2 * (a + b) + (b - c)^2 * (b + c) + (c - a)^2 * (c + a)) := @solution
#print axioms solution

-- Prove2me | solution 1 for WorkbookSource.problem_10948
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:50:22.575781+00:00
-- url     : https://prove2.me/submissions/55fd0389-4caa-43b6-b74f-a5903fe8277f

/- InternLM Lean-Workbook, lean_workbook_10948, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (a b : ℝ) (h1 : 0 < a ∧ 0 < b) (h2 : a ≤ 3 * b) (h3 : 3 * b ≤ 5 * a) : a^2 + b^2 ≤ (10/3) * a * b  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | nlinarith [h3]
  | solve
    | nlinarith [h3, h2]
  | solve
    | nlinarith only [h1, h2, h3]
  | solve
    | nlinarith [h2,h3,h1.1,h1.2]
example : (∀ (a b : ℝ) (h1 : 0 < a ∧ 0 < b) (h2 : a ≤ 3 * b) (h3 : 3 * b ≤ 5 * a), a^2 + b^2 ≤ (10/3) * a * b) := @solution
#print axioms solution

-- Prove2me | solution 1 for WorkbookSource.problem_53369
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:10:07.456926+00:00
-- url     : https://prove2.me/submissions/3c0440fa-0876-4e95-89d9-41b593bc5c7c

/- InternLM Lean-Workbook, lean_workbook_53369, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (a b c d : ℝ) (h1 : a > c) (h2 : b > d) : (a + b + c + d)^2 > 8 * (a * d + b * c)  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | ring_nf
      nlinarith [sq_nonneg (a + c - b - d)]
example : (∀ (a b c d : ℝ) (h1 : a > c) (h2 : b > d), (a + b + c + d)^2 > 8 * (a * d + b * c)) := @solution
#print axioms solution

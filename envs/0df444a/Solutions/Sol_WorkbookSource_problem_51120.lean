-- Prove2me | solution 1 for WorkbookSource.problem_51120
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:09:59.164818+00:00
-- url     : https://prove2.me/submissions/84ec7194-dfc9-467f-8596-19def5b82c37

/- InternLM Lean-Workbook, lean_workbook_51120, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (a : ℝ) : a^4 - 6*a^3 + 12*a^2 - 9*a + 3 > 0  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | nlinarith [sq_nonneg (a^2 - 3 * a + 1)]
  | solve
    | nlinarith [pow_two_nonneg (a^2 - 3*a + 1)]
  | solve
    | ring_nf
      nlinarith [sq_nonneg (a^2 - 3*a + 2)]
  | solve
    | ring_nf
      nlinarith [sq_nonneg (a^2 - 3 * a + 2)]
example : (∀ (a : ℝ), a^4 - 6*a^3 + 12*a^2 - 9*a + 3 > 0) := @solution
#print axioms solution

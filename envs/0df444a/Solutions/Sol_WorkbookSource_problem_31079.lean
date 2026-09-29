-- Prove2me | solution 1 for WorkbookSource.problem_31079
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:59:20.261621+00:00
-- url     : https://prove2.me/submissions/22a41cb4-c988-44ab-8161-20ab09e8a184

/- InternLM Lean-Workbook, lean_workbook_31079, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : Real.sqrt (2 * (a^2 + b^2) * (b^2 + c^2) * (c^2 + a^2)) ≥ (a + b) * (b + c) * (c + a) - 4 * a * b * c  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | have := sq_nonneg ((a - b) * (b - c) * (c - a))
      apply le_sqrt_of_sq_le
      linarith [ha, hb, hc]
  | solve
    | have := sq_nonneg ((a - b) * (b - c) * (c - a))
      apply le_sqrt_of_sq_le
      nlinarith [ha, hb, hc]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), Real.sqrt (2 * (a^2 + b^2) * (b^2 + c^2) * (c^2 + a^2)) ≥ (a + b) * (b + c) * (c + a) - 4 * a * b * c) := @solution
#print axioms solution

-- Prove2me | solution 1 for WorkbookSource.problem_6826
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:41:15.236756+00:00
-- url     : https://prove2.me/submissions/dbfcf762-e0c9-4c72-a6a4-90bb6c6f4992

/- InternLM Lean-Workbook, lean_workbook_6826, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (a b c : ℝ) : (a^2 + 2 * a * b + 3 * b^2) * (b^2 + 2 * b * c + 3 * c^2) * (c^2 + 2 * c * a + 3 * a^2) ≥ 8 * (a^2 + a * b + b * c) * (b^2 + b * c + c * a) * (c^2 + c * a + a * b)  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | have := sq_nonneg ((b - c) * (c - a) * (a - b))
      have := sq_nonneg (a * b * (a - b) + b * c * (b - c) + c * a * (c - a))
      have := sq_nonneg (a * b * (c - a) + b * c * (a - b) + c * a * (b - c))
      have := sq_nonneg (a^2 * (b - c)^2 + b^2 * (c - a)^2 + c^2 * (a - b)^2)
      have := sq_nonneg (a^2 * (c - b)^2 + b^2 * (a - c)^2 + c^2 * (b - a)^2)
      have := sq_nonneg (a * b * (a * (b - c)^2 + c * (c - a)^2) + b * c * (b * (c - a)^2 + c * (a - b)^2) + c * a * (c * (a - b)^2 + a * (b - c)^2))
      have := sq_nonneg (a * b * (b * (c - a)^2 + c * (a - b)^2) + b * c * (c * (a - b)^2 + a * (b - c)^2) + c * a * (a * (b - c)^2 + b * (c - a)^2))
      have := sq_nonneg (a^2 * (b * (c - a) * (a - b) + c * (a - b) * (b - c)) + b^2 * (c * (b - c) * (a - b) + a * (b - c) * (c - a)) + c^2 * (a * (c - a) * (b - c) + b * (c - a) * (a - b)))
      have := sq_nonneg (a^2 * (c * (a - b) * (a - b) + b * (a - b) * (b - c)) + b^2 * (a * (b - c) * (a - b) + c * (a - b) * (c - a)) + c^2 * (b * (c - a) * (a - b) + a * (c - a) * (b - c)))
      linarith
  | solve
    | have := sq_nonneg ((b - c) * (c - a) * (a - b))
      have := sq_nonneg (a * b * (a - b) + b * c * (b - c) + c * a * (c - a))
      have := sq_nonneg (a * b * (c - a) + b * c * (a - b) + c * a * (b - c))
      have := sq_nonneg (a^2 * (b - c)^2 + b^2 * (c - a)^2 + c^2 * (a - b)^2)
      have := sq_nonneg (a^2 * (c - b)^2 + b^2 * (a - c)^2 + c^2 * (b - a)^2)
      have := sq_nonneg (a * b * (a * (b - c)^2 + c * (c - a)^2) + b * c * (b * (c - a)^2 + c * (a - b)^2) + c * a * (c * (a - b)^2 + a * (b - c)^2))
      have := sq_nonneg (a * b * (b * (c - a)^2 + c * (a - b)^2) + b * c * (c * (a - b)^2 + a * (b - c)^2) + c * a * (a * (b - c)^2 + b * (c - a)^2))
      have := sq_nonneg (a^2 * (b * (c - a) * (a - b) + c * (a - b) * (b - c)) + b^2 * (c * (b - c) * (a - b) + a * (b - c) * (c - a)) + c^2 * (a * (c - a) * (b - c) + b * (c - a) * (a - b)))
      have := sq_nonneg (a^2 * (c * (a - b) * (a - b) + b * (a - b) * (b - c)) + b^2 * (a * (b - c) * (a - b) + c * (a - b) * (c - a)) + c^2 * (b * (c - a) * (a - b) + a * (c - a) * (b - c)))
      nlinarith
example : (∀ (a b c : ℝ), (a^2 + 2 * a * b + 3 * b^2) * (b^2 + 2 * b * c + 3 * c^2) * (c^2 + 2 * c * a + 3 * a^2) ≥ 8 * (a^2 + a * b + b * c) * (b^2 + b * c + c * a) * (c^2 + c * a + a * b)) := @solution
#print axioms solution

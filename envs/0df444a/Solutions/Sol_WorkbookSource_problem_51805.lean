-- Prove2me | solution 1 for WorkbookSource.problem_51805
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:10:04.346271+00:00
-- url     : https://prove2.me/submissions/63e7698c-1152-4e63-8de4-332970e8212f

/- InternLM Lean-Workbook, lean_workbook_51805, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (a b c : ℝ) : a^6 + b^6 + c^6 + a^4 * b^2 + b^4 * c^2 + c^4 * a^2 ≥ 2 * (a^3 * b^2 * c + b^3 * c^2 * a + c^3 * a^2 * b)  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | -- Using AM-GM inequality
      nlinarith [sq_nonneg (a^3 - b^2 * c), sq_nonneg (b^3 - c^2 * a), sq_nonneg (c^3 - a^2 * b)]
  | solve
    | have h1 := sq_nonneg (a^3 - b^2 * c)
      have h2 := sq_nonneg (b^3 - c^2 * a)
      have h3 := sq_nonneg (c^3 - a^2 * b)
      linarith
  | solve
    | have h1 := sq_nonneg (a^3 - b^2 * c)
      have h2 := sq_nonneg (b^3 - c^2 * a)
      have h3 := sq_nonneg (c^3 - a^2 * b)
      nlinarith
example : (∀ (a b c : ℝ), a^6 + b^6 + c^6 + a^4 * b^2 + b^4 * c^2 + c^4 * a^2 ≥ 2 * (a^3 * b^2 * c + b^3 * c^2 * a + c^3 * a^2 * b)) := @solution
#print axioms solution

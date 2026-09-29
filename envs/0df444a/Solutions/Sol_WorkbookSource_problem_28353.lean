-- Prove2me | solution 1 for WorkbookSource.problem_28353
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:57:16.952898+00:00
-- url     : https://prove2.me/submissions/ef3a9d5a-d529-43d4-85ac-14019c16b27d

/- InternLM Lean-Workbook, lean_workbook_28353, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (a : ℝ) (h1: a ≥ -2 ∧ a ≤ 2) : a^3 ≥ 3*a - 2  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | nlinarith [h1.1, h1.2, sq_nonneg (a-1)]
  | solve
    | nlinarith [sq_nonneg (a - 1), sq_nonneg (a + 2)]
  | solve
    | nlinarith [sq_nonneg (a + 1), sq_nonneg (a - 1)]
  | solve
    | have h2 := sq_nonneg (a-1)
      nlinarith [h1.1, h1.2, h2]
example : (∀ (a : ℝ) (h1: a ≥ -2 ∧ a ≤ 2), a^3 ≥ 3*a - 2) := @solution
#print axioms solution

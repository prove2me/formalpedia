-- Prove2me | solution 1 for WorkbookSource.problem_53513
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:10:08.986858+00:00
-- url     : https://prove2.me/submissions/d2dfaf3b-87c4-4528-971e-9863ead5de80

/- InternLM Lean-Workbook, lean_workbook_53513, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (y : ℝ) (hy : -2 ≤ y ∧ y ≤ 1) : y^2 + y - 2 ≤ 0  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | nlinarith only [hy]
  | solve
    | nlinarith [hy.1, hy.2]
  | solve
    | rw [← sub_nonneg]
      nlinarith
  | solve
    | simp [sq]
      nlinarith [hy.1, hy.2]
example : (∀ (y : ℝ) (hy : -2 ≤ y ∧ y ≤ 1), y^2 + y - 2 ≤ 0) := @solution
#print axioms solution

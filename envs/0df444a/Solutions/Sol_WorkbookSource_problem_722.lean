-- Prove2me | solution 1 for WorkbookSource.problem_722
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:40:56.163795+00:00
-- url     : https://prove2.me/submissions/b1771d42-f26c-43bc-804b-d4cb38a49712

/- InternLM Lean-Workbook, lean_workbook_722, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution : ∀ x y z : ℝ, 16 * x ^ 2 + 25 * y ^ 2 + 36 * z ^ 2 ≥ 45 * y * z + 27 * z * x + 5 * x * y  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | intro x y z
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (x - z)]
  | solve
    | intro x y z
      simp [sq]
      linarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]
  | solve
    | intro x y z
      simp [sq]
      nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]
example : (∀ x y z : ℝ, 16 * x ^ 2 + 25 * y ^ 2 + 36 * z ^ 2 ≥ 45 * y * z + 27 * z * x + 5 * x * y) := @solution
#print axioms solution

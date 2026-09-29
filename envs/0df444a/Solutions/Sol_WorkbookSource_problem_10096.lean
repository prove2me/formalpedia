-- Prove2me | solution 1 for WorkbookSource.problem_10096
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:50:19.468325+00:00
-- url     : https://prove2.me/submissions/0095decf-6c24-49e3-beb7-052b1a8c8f50

/- InternLM Lean-Workbook, lean_workbook_10096, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) : (3 / 2) * (x + y + z) * (3 * (x + y + z) ^ 2 + x * y + x * z + y * z) ≥ (3 * x + y + z) * (3 * y + x + z) * (3 * z + x + y)  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  | solve
    | have := sq_nonneg (x - y)
      have := sq_nonneg (y - z)
      have := sq_nonneg (z - x)
      nlinarith
example : (∀ (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0), (3 / 2) * (x + y + z) * (3 * (x + y + z) ^ 2 + x * y + x * z + y * z) ≥ (3 * x + y + z) * (3 * y + x + z) * (3 * z + x + y)) := @solution
#print axioms solution

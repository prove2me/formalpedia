-- Prove2me | solution 1 for WorkbookSource.problem_31792
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:59:21.008322+00:00
-- url     : https://prove2.me/submissions/95fbedd1-dc71-4e31-8a08-96b50b46fff8

/- InternLM Lean-Workbook, lean_workbook_31792, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (x y z : ℝ) (hx : -2 ≤ x) (hy : -2 ≤ y) (hz : -2 ≤ z) (h : x^3 + y^3 + z^3 ≥ x^2 + y^2 + z^2) : x^5 + y^5 + z^5 ≥ x^2 + y^2 + z^2  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | nlinarith [sq_nonneg (x^2 - x), sq_nonneg (y^2 - y), sq_nonneg (z^2 - z), hx, hy, hz, h]
  | solve
    | have h2 := sq_nonneg (x^2 - x)
      have h2' := sq_nonneg (y^2 - y)
      have h2'' := sq_nonneg (z^2 - z)
      nlinarith
example : (∀ (x y z : ℝ) (hx : -2 ≤ x) (hy : -2 ≤ y) (hz : -2 ≤ z) (h : x^3 + y^3 + z^3 ≥ x^2 + y^2 + z^2), x^5 + y^5 + z^5 ≥ x^2 + y^2 + z^2) := @solution
#print axioms solution

-- Prove2me | solution 1 for WorkbookSource.problem_16555
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:39:40.406389+00:00
-- url     : https://prove2.me/submissions/981db6f0-24be-4eb7-87d1-f6ec2cf7f941

/- InternLM Lean-Workbook, lean_workbook_16555, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution : ∀ x y z : ℝ, 6 * (x^4 + y^4 + z^4) + 9 * (x^2 * y^2 + x^2 * z^2 + y^2 * z^2) + 6 * (x^3 * y + x^3 * z + y^3 * x + y^3 * z + z^3 * x + z^3 * y) ≥ (x + y + z)^4  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | rintro x y z
      nlinarith [sq_nonneg (x + y + z), sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
example : (∀ x y z : ℝ, 6 * (x^4 + y^4 + z^4) + 9 * (x^2 * y^2 + x^2 * z^2 + y^2 * z^2) + 6 * (x^3 * y + x^3 * z + y^3 * x + y^3 * z + z^3 * x + z^3 * y) ≥ (x + y + z)^4) := @solution
#print axioms solution

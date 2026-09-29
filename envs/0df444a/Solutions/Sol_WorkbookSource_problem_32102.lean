-- Prove2me | solution 1 for WorkbookSource.problem_32102
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:59:24.308976+00:00
-- url     : https://prove2.me/submissions/2d08895a-cca0-413c-9bcd-58f094ba0fc3

/- InternLM Lean-Workbook, lean_workbook_32102, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (x y z : ℝ) (hx : x + y + z = 1) (hx' : 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z) : 8 ≤ (x + 1) * (y + 2) * (z + 3) ∧ (x + 1) * (y + 2) * (z + 3) ≤ 12  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | constructor
      nlinarith [mul_nonneg hx'.2.1 hx'.2.2, hx]
      nlinarith [mul_nonneg hx'.2.1 hx'.2.2, hx]
example : (∀ (x y z : ℝ) (hx : x + y + z = 1) (hx' : 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z), 8 ≤ (x + 1) * (y + 2) * (z + 3) ∧ (x + 1) * (y + 2) * (z + 3) ≤ 12) := @solution
#print axioms solution

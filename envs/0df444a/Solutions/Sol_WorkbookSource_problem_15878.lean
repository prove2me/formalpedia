-- Prove2me | solution 1 for WorkbookSource.problem_15878
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:39:44.847375+00:00
-- url     : https://prove2.me/submissions/3c5f4710-616c-4ec2-8192-143c98e9b6dc

/- InternLM Lean-Workbook, lean_workbook_15878, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 10000
set_option exponentiation.threshold 4096
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (a b c : ℝ) (h : (a+b)^2 + (b+c)^2 + (c+a)^2 = 3) : 2 * (b+c)^2 ≤ 6 - (2*a + b + c)^2 ∧ 6 - (2*a + b + c)^2 ≤ 4 * (b^2 + c^2)  := by
  constructor <;> nlinarith [sq_nonneg (b-c)]
example : (∀ (a b c : ℝ) (h : (a+b)^2 + (b+c)^2 + (c+a)^2 = 3), 2 * (b+c)^2 ≤ 6 - (2*a + b + c)^2 ∧ 6 - (2*a + b + c)^2 ≤ 4 * (b^2 + c^2)) := @solution
#print axioms solution

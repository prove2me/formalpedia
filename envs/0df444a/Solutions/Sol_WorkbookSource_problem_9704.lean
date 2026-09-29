-- Prove2me | solution 1 for WorkbookSource.problem_9704
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:50:12.834279+00:00
-- url     : https://prove2.me/submissions/969ee66b-1d0e-4134-a95f-355e1ed94a59

/- InternLM Lean-Workbook, lean_workbook_9704, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (a b c d : ℝ) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) : (a + b + c + d) ^ 2 ≥ 8 * (a * c + b * d)  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | ring_nf
      rw [add_comm]
      nlinarith [sq_nonneg (b + c - a - d)]
example : (∀ (a b c d : ℝ) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d), (a + b + c + d) ^ 2 ≥ 8 * (a * c + b * d)) := @solution
#print axioms solution

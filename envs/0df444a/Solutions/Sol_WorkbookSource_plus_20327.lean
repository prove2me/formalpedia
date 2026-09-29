-- Prove2me | solution 1 for WorkbookSource.plus_20327
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:10:11.346717+00:00
-- url     : https://prove2.me/submissions/1b1c6778-73e5-4714-a755-278f76ac36b3

/- InternLM Lean-Workbook, lean_workbook_plus_20327, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution : ¬ (∃ x : ℝ, 8*x^8 + 3*x^6 + 5*x^4 + 3*x^2 + 10 = 0)   := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | refine' not_exists.2 fun x => _
      positivity
  | solve
    | simp [sq]
      intro x
      nlinarith [sq_nonneg (x ^ 2)]
  | solve
    | simp [add_comm]
      intro x
      nlinarith [sq_nonneg (x ^ 2)]
  | solve
    | simp [add_assoc]
      intro x
      nlinarith [sq_nonneg (x ^ 2)]
example : (¬ (∃ x : ℝ, 8*x^8 + 3*x^6 + 5*x^4 + 3*x^2 + 10 = 0)) := @solution
#print axioms solution

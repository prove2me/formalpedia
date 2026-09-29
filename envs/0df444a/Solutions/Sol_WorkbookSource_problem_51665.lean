-- Prove2me | solution 1 for WorkbookSource.problem_51665
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:10:03.56502+00:00
-- url     : https://prove2.me/submissions/1179f9bc-eaea-4362-9f85-f7151f30a5c1

/- InternLM Lean-Workbook, lean_workbook_51665, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution  (x : ℝ)
  (h₀ : 1 < x) :
  11 * x^3 + 2 * x^6 + 2 ≥ 10 * x^2 + 5 * x^5  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | nlinarith [pow_two_nonneg (x - 1), pow_two_nonneg (x^2 - 1), pow_two_nonneg (x^3 - 1)]
example : (∀ (x : ℝ)
  (h₀ : 1 < x), 11 * x^3 + 2 * x^6 + 2 ≥ 10 * x^2 + 5 * x^5) := @solution
#print axioms solution

-- Prove2me | solution 1 for WorkbookSource.problem_3104
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:41:04.88706+00:00
-- url     : https://prove2.me/submissions/62c03a9f-1d65-4b59-8c20-0f89a787cbdc

/- InternLM Lean-Workbook, lean_workbook_3104, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (x : ℝ) (hx : 1 ≤ x) : (x^2 - 1) * (x^2 + 4 * x + 1) - 12 * Real.log x ≥ 0  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | have h1 : 0 ≤ x^2 - 1 := by nlinarith
      nlinarith [Real.log_le_sub_one_of_pos (by positivity)]
  | solve
    | have h1 : 0 ≤ (x - 1)^2 := sq_nonneg (x - 1)
      nlinarith [Real.log_le_sub_one_of_pos (by positivity)]
  | solve
    | have : 0 ≤ (x - 1)^2 := sq_nonneg (x - 1)
      nlinarith [Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hx)]
  | solve
    | have := sq_nonneg (x - 1)
      have := sq_nonneg (x + 1)
      nlinarith [Real.log_le_sub_one_of_pos (by positivity)]
example : (∀ (x : ℝ) (hx : 1 ≤ x), (x^2 - 1) * (x^2 + 4 * x + 1) - 12 * Real.log x ≥ 0) := @solution
#print axioms solution

-- Prove2me | solution 1 for WorkbookSource.problem_39879
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T13:06:31.486724+00:00
-- url     : https://prove2.me/submissions/55881127-a7fc-483b-8dba-307fc988e991

/- Source: InternLM Lean-Workbook, record lean_workbook_39879.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json
Apache-2.0. Complete original proposition preserved. Proof compatibility changes, if any, are documented in the explanation. -/
import Mathlib
open Real
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem solution (x : ℝ) (hx: x >= 0) : 3 * x^6 + 2 * x + 2 * x^2 + x^3 - x^4 - 2 * x^5 >= 0 := by
  first
  | solve
    | nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg (x ^ 3 - 1)]
  | solve
    | simp [add_comm]
      nlinarith [sq_nonneg (x^3 - x^2), sq_nonneg (x^2 - 1)]
  | solve
    | nlinarith [pow_nonneg hx 3, pow_nonneg hx 4, pow_nonneg hx 5, pow_nonneg hx 6]
  | solve
    | have h1: 0 ≤ x^6 := pow_nonneg hx 6
      have h2: x^3 ≥ 0 := pow_nonneg hx 3
      nlinarith
  | solve
    | have h1 := sq_nonneg (x^3 - x^2)
      have h2 := sq_nonneg (x^2 - 1)
      nlinarith [h1, h2]

example : (∀ (x : ℝ) (hx: x >= 0), 3 * x^6 + 2 * x + 2 * x^2 + x^3 - x^4 - 2 * x^5 >= 0) := @solution
#print axioms solution

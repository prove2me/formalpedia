-- Prove2me | solution 1 for WorkbookSource.problem_55336
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T13:06:44.39693+00:00
-- url     : https://prove2.me/submissions/f1059938-3cdb-41fa-bf9f-f8863cef57e3

/- Source: InternLM Lean-Workbook, record lean_workbook_55336.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json
Apache-2.0. Complete original proposition preserved. Proof compatibility changes, if any, are documented in the explanation. -/
import Mathlib
open Real
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem solution (x : ℝ) (hx : 0 ≤ x) : x ^ 3 + 15 * x ≥ 7 * x ^ 2 := by
  first
  | solve
    | nlinarith [sq_nonneg (x ^ 2 - 3 * x)]
  | solve
    | nlinarith [sq_nonneg (x ^ 2 - 3 * x - 3)]
  | solve
    | nlinarith [sq_nonneg (x - 3), sq_nonneg (x - 5)]
  | solve
    | have := sq_nonneg (x ^ 2 - 3 * x)
      nlinarith [hx]
  | solve
    | nlinarith [sq_nonneg (x - 5), sq_nonneg (x - 3)]
  | solve
    | have : 0 ≤ (x - 3) ^ 2 * (x + 5) := by nlinarith
      nlinarith

example : (∀ (x : ℝ) (hx : 0 ≤ x), x ^ 3 + 15 * x ≥ 7 * x ^ 2) := @solution
#print axioms solution

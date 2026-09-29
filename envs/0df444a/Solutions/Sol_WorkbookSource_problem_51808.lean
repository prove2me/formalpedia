-- Prove2me | solution 1 for WorkbookSource.problem_51808
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T13:06:38.87106+00:00
-- url     : https://prove2.me/submissions/6b2652a6-0342-4fd5-8600-a120a860e2aa

/- Source: InternLM Lean-Workbook, record lean_workbook_51808.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json
Apache-2.0. Complete original proposition preserved. Proof compatibility changes, if any, are documented in the explanation. -/
import Mathlib
open Real
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem solution (x : ℝ) (h : x >= 2) : x^3 + 1 > 2 * x^2 := by
  first
  | solve
    | nlinarith [h]
  | solve
    | nlinarith [h, h]
  | solve
    | nlinarith only [h]
  | solve
    | nlinarith [pow_two_nonneg x]
  | solve
    | rw [pow_three]
      nlinarith [h, h]
  | solve
    | repeat' rw [pow_two]
      nlinarith [h]

example : (∀ (x : ℝ) (h : x >= 2), x^3 + 1 > 2 * x^2) := @solution
#print axioms solution

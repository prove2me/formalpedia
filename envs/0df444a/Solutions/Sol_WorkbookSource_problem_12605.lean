-- Prove2me | solution 1 for WorkbookSource.problem_12605
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:17:45.021962+00:00
-- url     : https://prove2.me/submissions/aa15088e-7fc2-4de2-b2f8-8f53589aee5b

/- Source: InternLM Lean-Workbook, record lean_workbook_12605.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json
Apache-2.0. Original statement and candidate proofs preserved. -/
import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem solution (a b c : ℝ) (ha : a^3 + b^3 + c^3 - 1 = 3 * (a - 1) * (b - 1) * (c - 1)) : a + b + c ≤ 2 := by
  first
  | solve
    | have := sq_nonneg (a - b)
      have := sq_nonneg (b - c)
      have := sq_nonneg (c - a)
      nlinarith

example : (∀ (a b c : ℝ) (ha : a^3 + b^3 + c^3 - 1 = 3 * (a - 1) * (b - 1) * (c - 1)), a + b + c ≤ 2) := @solution
#print axioms solution

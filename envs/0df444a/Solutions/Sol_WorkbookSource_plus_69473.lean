-- Prove2me | solution 1 for WorkbookSource.plus_69473
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T13:16:36.698744+00:00
-- url     : https://prove2.me/submissions/5b29a8ec-79e3-4d05-b7c0-8c9e032ed94a

/- Source: InternLM Lean-Workbook, record lean_workbook_plus_69473.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json
Apache-2.0. Complete original proposition and source candidate proof preserved. -/
import Mathlib
open Real
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (habc : a + b + c = 1) : a^2 + 4 * b * c ≤ 1 := by
  first
  | solve
    | nlinarith [sq_nonneg (b - c)]

example : (∀ (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (habc : a + b + c = 1), a^2 + 4 * b * c ≤ 1) := @solution
#print axioms solution

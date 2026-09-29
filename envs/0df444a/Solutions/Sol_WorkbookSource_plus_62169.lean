-- Prove2me | solution 1 for WorkbookSource.plus_62169
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T13:16:34.446968+00:00
-- url     : https://prove2.me/submissions/811488a4-d139-49b9-a41c-9787c9a827b8

/- Source: InternLM Lean-Workbook, record lean_workbook_plus_62169.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json
Apache-2.0. Complete original proposition and source candidate proof preserved. -/
import Mathlib
open Real
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : 4 * a ^ 2 + 2 * b ^ 4 + c ^ 8 + d ^ 8 ≥ 8 * a * b * c * d := by
  first
  | solve
    | nlinarith [sq_nonneg (a - b * c * d), sq_nonneg (b ^ 2 - c ^ 2 * d ^ 2), sq_nonneg (c ^ 4 - d ^ 4)]

example : (∀ (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d), 4 * a ^ 2 + 2 * b ^ 4 + c ^ 8 + d ^ 8 ≥ 8 * a * b * c * d) := @solution
#print axioms solution

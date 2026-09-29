-- Prove2me | solution 1 for WorkbookSource.plus_50825
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T13:16:32.913779+00:00
-- url     : https://prove2.me/submissions/5463e00d-9a18-42a1-80f1-039742c2ee22

/- Source: InternLM Lean-Workbook, record lean_workbook_plus_50825.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json
Apache-2.0. Complete original proposition and source candidate proof preserved. -/
import Mathlib
open Real
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c^2 = 4) : a^2 + b^2 + c^2 ≥ 7 / 2 := by
  first
  | solve
    | nlinarith [sq_nonneg (a - 1/2), sq_nonneg (b - 1/2), sq_nonneg (c - 1/2)]

example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c^2 = 4), a^2 + b^2 + c^2 ≥ 7 / 2) := @solution
#print axioms solution

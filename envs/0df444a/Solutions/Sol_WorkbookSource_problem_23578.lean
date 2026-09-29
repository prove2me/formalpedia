-- Prove2me | solution 1 for WorkbookSource.problem_23578
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:41:53.710583+00:00
-- url     : https://prove2.me/submissions/e7f5ed3e-31f9-454f-a42a-6b3f53d20970

/- Source: InternLM Lean-Workbook, record lean_workbook_23578.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json
Apache-2.0. Complete original proposition preserved; source candidate proof adapted only for Mathlib compatibility where documented. -/
import Mathlib
open Real
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem solution (a b c : ℝ) : (a - b) ^ 4 + (b - c) ^ 4 + (c - a) ^ 4 ≥ 8 * (a - b) ^ 2 * (c - a) * (c - b) := by
  first
  | solve
    | have := sq_nonneg ((a - b) ^ 2 - (c - a) * (c - b))
      linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]

example : (∀ (a b c : ℝ), (a - b) ^ 4 + (b - c) ^ 4 + (c - a) ^ 4 ≥ 8 * (a - b) ^ 2 * (c - a) * (c - b)) := @solution
#print axioms solution

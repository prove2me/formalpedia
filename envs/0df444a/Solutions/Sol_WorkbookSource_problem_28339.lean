-- Prove2me | solution 1 for WorkbookSource.problem_28339
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:41:56.028664+00:00
-- url     : https://prove2.me/submissions/e3d75a3c-6272-499f-a102-7316059280ca

/- Source: InternLM Lean-Workbook, record lean_workbook_28339.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json
Apache-2.0. Complete original proposition preserved; source candidate proof adapted only for Mathlib compatibility where documented. -/
import Mathlib
open Real
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem solution (x : ℝ) (h : x ≥ 2) : x^2 + 2 * Real.sqrt (x + 2) - 3 * x ≥ 2 := by
  first
  | solve
    | have : Real.sqrt (x + 2) ≥ 2 := by apply Real.le_sqrt_of_sq_le; linarith
      nlinarith [h, this]

example : (∀ (x : ℝ) (h : x ≥ 2), x^2 + 2 * Real.sqrt (x + 2) - 3 * x ≥ 2) := @solution
#print axioms solution

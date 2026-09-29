-- Prove2me | solution 1 for WorkbookSource.problem_773
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:17:41.970723+00:00
-- url     : https://prove2.me/submissions/3aab361b-773d-4fed-abbc-5cc9d3490dcc

/- Source: InternLM Lean-Workbook, record lean_workbook_773.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json
Apache-2.0. Original statement and candidate proof preserved. -/
import Mathlib
set_option autoImplicit false
theorem solution (a b c : ℝ) : (a^2 + 1) * (b^2 + 1) * (c^2 + 1) ≥ (a * b * c - 1)^2 := by
  simp [sq]
  ring_nf
  nlinarith [sq_nonneg (a * b * c), sq_nonneg (a * b + c)]

example : (∀ (a b c : ℝ), (a^2 + 1) * (b^2 + 1) * (c^2 + 1) ≥ (a * b * c - 1)^2) := @solution
#print axioms solution

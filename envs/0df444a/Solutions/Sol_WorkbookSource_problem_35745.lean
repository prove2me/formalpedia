-- Prove2me | solution 1 for WorkbookSource.problem_35745
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:44:29.885713+00:00
-- url     : https://prove2.me/submissions/55f81f09-f313-4255-9e87-1e00165036d4

/- Source: InternLM Lean-Workbook, record lean_workbook_35745.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json
Apache-2.0. Complete original proposition preserved; source candidate proof adapted only for Mathlib compatibility where documented. -/
import Mathlib
open Real
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem solution (x y : ℝ) : (sin (x + y))^2 ≥ sin (2*x) * sin (2*y) := by
  first
  | solve
    | simp [two_mul, sin_add, cos_add]
      have := sq_nonneg (sin x * cos y - cos x * sin y)
      linarith [sq_nonneg (sin x * cos y - cos x * sin y)]

example : (∀ (x y : ℝ), (sin (x + y))^2 ≥ sin (2*x) * sin (2*y)) := @solution
#print axioms solution

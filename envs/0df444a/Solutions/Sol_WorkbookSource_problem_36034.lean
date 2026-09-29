-- Prove2me | solution 1 for WorkbookSource.problem_36034
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:44:30.630363+00:00
-- url     : https://prove2.me/submissions/83da3f79-05ee-410f-89c5-6dc89504050a

/- Source: InternLM Lean-Workbook, record lean_workbook_36034.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json
Apache-2.0. Complete original proposition preserved; source candidate proof adapted only for Mathlib compatibility where documented. -/
import Mathlib
open Real
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem solution (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1) :
  (1 - a) * (1 - b) ≥ c * d := by
  first
  | solve
    | linarith [sq_nonneg (1 - a - b), sq_nonneg (c - d), h]
  | solve
    | have h2 : 0 ≤ (a + b - 1)^2 + (c - d)^2 := by nlinarith
      linarith
  | solve
    | have : 0 ≤ (a + b - 1)^2 + (c - d)^2 := by positivity
      linarith [h]
  | solve
    | have h1 : 0 ≤ (a + b - 1)^2 + (c - d)^2 := by positivity
      linarith [h]
  | solve
    | have h2 : 0 ≤ (a + b - 1)^2 + (c - d)^2 := by positivity
      linarith [h]
  | solve
    | have h1 := sq_nonneg (1 - a - b)
      have h2 := sq_nonneg (c - d)
      linarith

example : (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), (1 - a) * (1 - b) ≥ c * d) := @solution
#print axioms solution

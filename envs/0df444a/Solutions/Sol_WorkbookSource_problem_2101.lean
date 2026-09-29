-- Prove2me | solution 1 for WorkbookSource.problem_2101
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:17:42.699659+00:00
-- url     : https://prove2.me/submissions/f8ecb31b-4ea8-4e80-abc5-9ee23c22c530

/- Source: InternLM Lean-Workbook, record lean_workbook_2101.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json
Apache-2.0. Original statement and candidate proof preserved. -/
import Mathlib
set_option autoImplicit false
theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (h : x^3 + y^3 ≤ x - y) : x^2 + y^2 ≤ 1 := by
  nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), h]

example : (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (h : x^3 + y^3 ≤ x - y), x^2 + y^2 ≤ 1) := @solution
#print axioms solution

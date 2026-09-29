-- Prove2me | solution 1 for WorkbookSource.plus_67328
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T13:16:35.925648+00:00
-- url     : https://prove2.me/submissions/5c1ff67b-4de0-42bc-ae1e-0745a5ac43bd

/- Source: InternLM Lean-Workbook, record lean_workbook_plus_67328.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json
Apache-2.0. Complete original proposition and source candidate proof preserved. -/
import Mathlib
open Real
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem solution (x y : ℝ) (h : x^2 + 2*y^2 - x*y = 75) : x^2 + 4*y^2 - 2*x*y ≥ 450/7 := by
  first
  | solve
    | nlinarith [sq_nonneg (x - 4 * y)]

example : (∀ (x y : ℝ) (h : x^2 + 2*y^2 - x*y = 75), x^2 + 4*y^2 - 2*x*y ≥ 450/7) := @solution
#print axioms solution

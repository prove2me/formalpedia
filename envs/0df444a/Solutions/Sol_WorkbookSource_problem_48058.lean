-- Prove2me | solution 1 for WorkbookSource.problem_48058
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T13:06:35.96063+00:00
-- url     : https://prove2.me/submissions/e612eef6-e13e-4603-b40b-baeca4faf355

/- Source: InternLM Lean-Workbook, record lean_workbook_48058.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json
Apache-2.0. Complete original proposition preserved. Proof compatibility changes, if any, are documented in the explanation. -/
import Mathlib
open Real
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem solution (b : ℝ) : b^6 + b^4 + b^2 + 1 ≥ (1 + b^3)^2 := by
  first
  | solve
    | simp [sq, add_assoc, add_comm, add_left_comm]
      nlinarith [sq_nonneg (b - 1), sq_nonneg (b^2 - 1)]

example : (∀ (b : ℝ), b^6 + b^4 + b^2 + 1 ≥ (1 + b^3)^2) := @solution
#print axioms solution

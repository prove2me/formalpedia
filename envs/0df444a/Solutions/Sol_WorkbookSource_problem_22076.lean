-- Prove2me | solution 1 for WorkbookSource.problem_22076
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:41:52.158935+00:00
-- url     : https://prove2.me/submissions/c0676e34-7163-43cd-892d-af5ba64bb19f

/- Source: InternLM Lean-Workbook, record lean_workbook_22076.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json
Apache-2.0. Complete original proposition preserved; source candidate proof adapted only for Mathlib compatibility where documented. -/
import Mathlib
open Real
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem solution (x y z : ℝ) : x^4 + 1 + y^4 + z^2 + 2 * x^2 ≥ 2 * x^2 * y^2 + 2 * x * z + 2 * x := by
  first
  | solve
    | rw [add_assoc]
      nlinarith [sq_nonneg (x^2 - y^2), sq_nonneg (x - z), sq_nonneg (x - 1)]
  | solve
    | have h1 : 0 ≤ (x^2 - y^2)^2 := sq_nonneg (x^2 - y^2)
      have h2 := sq_nonneg (x - z)
      have h3 := sq_nonneg (1 - x)
      nlinarith

example : (∀ (x y z : ℝ), x^4 + 1 + y^4 + z^2 + 2 * x^2 ≥ 2 * x^2 * y^2 + 2 * x * z + 2 * x) := @solution
#print axioms solution

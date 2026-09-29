-- Prove2me | solution 1 for WorkbookSource.problem_33047
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:44:26.722803+00:00
-- url     : https://prove2.me/submissions/7c09393a-059f-47df-811e-e6d6da5d6d7f

/- Source: InternLM Lean-Workbook, record lean_workbook_33047.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json
Apache-2.0. Complete original proposition preserved; source candidate proof adapted only for Mathlib compatibility where documented. -/
import Mathlib
open Real
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem solution (a : ℝ) : 3 * (a^2 + a + 1)^2 ≤ (a^2 + 2)^3 := by
  first
  | solve
    | nlinarith [sq_nonneg (a + 1), sq_nonneg (a - 1)]
  | solve
    | simp [sq]
      nlinarith [sq_nonneg (a + 1), sq_nonneg (a - 1)]
  | solve
    | field_simp [sq]
      nlinarith [sq_nonneg (a - 1), sq_nonneg (a + 1)]
  | solve
    | simp only [pow_two, pow_three]
      nlinarith [sq_nonneg (a - 1), sq_nonneg (a + 1)]

example : (∀ (a : ℝ), 3 * (a^2 + a + 1)^2 ≤ (a^2 + 2)^3) := @solution
#print axioms solution

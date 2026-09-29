-- Prove2me | solution 1 for WorkbookSource.problem_27795
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:44:22.248313+00:00
-- url     : https://prove2.me/submissions/6a3dc7c1-75ed-49ac-ae17-3cfe1c4068f1

/- Source: InternLM Lean-Workbook, record lean_workbook_27795.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json
Apache-2.0. Complete original proposition preserved; source candidate proof adapted only for Mathlib compatibility where documented. -/
import Mathlib
open Real
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem solution (x y : ℝ) (h₁ : x + y = 5) (h₂ : x * y = 2) : x^3 + y^3 = 95 := by
  first
  | solve
    | simp only [pow_three, h₁, h₂]
      nlinarith
  | solve
    | simp only [pow_three]
      nlinarith [h₁, h₂]
  | solve
    | field_simp [pow_three]
      nlinarith [h₁, h₂]
  | solve
    | simp [h₂, h₁, pow_succ]
      nlinarith [h₁, h₂]
  | solve
    | simp [h₂, pow_three, h₁]
      nlinarith [h₁, h₂]
  | solve
    | simp [pow_three, h₁, h₂, add_comm]
      nlinarith

example : (∀ (x y : ℝ) (h₁ : x + y = 5) (h₂ : x * y = 2), x^3 + y^3 = 95) := @solution
#print axioms solution

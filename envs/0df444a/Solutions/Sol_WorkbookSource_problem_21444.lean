-- Prove2me | solution 1 for WorkbookSource.problem_21444
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:41:51.368245+00:00
-- url     : https://prove2.me/submissions/21a24646-7635-4cbd-a534-b6278e5beba0

/- Source: InternLM Lean-Workbook, record lean_workbook_21444.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json
Apache-2.0. Complete original proposition preserved; source candidate proof adapted only for Mathlib compatibility where documented. -/
import Mathlib
open Real
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem solution (x y z : ℝ)
  (h₀ : 0 < x ∧ 0 < y ∧ 0 < z)
  (h₁ : x < y)
  (h₂ : y < z)
  (h₃ : z < 1) :
  x^2 + y^2 + z^2 < x * y + x * z + y * z + z - x := by
  first
  | solve
    | simp [sq]
      nlinarith

example : (∀ (x y z : ℝ)
  (h₀ : 0 < x ∧ 0 < y ∧ 0 < z)
  (h₁ : x < y)
  (h₂ : y < z)
  (h₃ : z < 1), x^2 + y^2 + z^2 < x * y + x * z + y * z + z - x) := @solution
#print axioms solution

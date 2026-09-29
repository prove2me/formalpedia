-- Prove2me | solution 1 for WorkbookSource.problem_57310
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:44:04.372682+00:00
-- url     : https://prove2.me/submissions/d2b1b4e7-8400-4b38-a974-ced4a89444e4

/- Source: InternLM Lean-Workbook lean_workbook_57310, Apache-2.0.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json -/
import Mathlib
open Nat Real
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1000
theorem solution  (x y : ℝ)
  (h₀ : x ≠ 1)
  (h₁ : 4 * x^2 + 7 * x * y = 7 * y + 2)
  (h₂ : 4 * x * y + 7 * y^2 = 4 * x + 2) :
  y = (2 * (1 - 2 * x^2)) / (7 * (x - 1)) := by
  have hd : 7*(x-1)≠0 := by positivity
  apply (eq_div_iff hd).2
  nlinarith [h₁]

example : (∀ (x y : ℝ)
  (h₀ : x ≠ 1)
  (h₁ : 4 * x^2 + 7 * x * y = 7 * y + 2)
  (h₂ : 4 * x * y + 7 * y^2 = 4 * x + 2), y = (2 * (1 - 2 * x^2)) / (7 * (x - 1))) := @solution
#print axioms solution

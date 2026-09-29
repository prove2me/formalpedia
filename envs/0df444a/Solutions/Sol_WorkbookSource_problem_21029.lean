-- Prove2me | solution 1 for WorkbookSource.problem_21029
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:15:06.990264+00:00
-- url     : https://prove2.me/submissions/766b41d9-bc41-42b9-89fa-5250b1e1b312

/- Source: InternLM Lean-Workbook lean_workbook_21029, Apache-2.0.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json -/
import Mathlib
open Nat Real
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a : ℕ) (r : ℚ) (n : ℕ) (h₁ : a = 4096) (h₂ : r = -1/2) (h₃ : n = 16) : ∑ i ∈ Finset.range n, a * r^i = 2730.625 := by
  simp only [h₁, h₂, h₃]
  norm_num [Finset.sum_range_succ]

example : (∀ (a : ℕ) (r : ℚ) (n : ℕ) (h₁ : a = 4096) (h₂ : r = -1/2) (h₃ : n = 16), ∑ i ∈ Finset.range n, a * r^i = 2730.625) := @solution
#print axioms solution

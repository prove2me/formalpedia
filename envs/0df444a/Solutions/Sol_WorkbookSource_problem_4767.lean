-- Prove2me | solution 1 for WorkbookSource.problem_4767
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:14:59.143288+00:00
-- url     : https://prove2.me/submissions/257ff49f-cfa9-457c-9ec6-94ab12f9acc8

/- Source: InternLM Lean-Workbook lean_workbook_4767, Apache-2.0.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json -/
import Mathlib
open Nat Real
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (n : ℕ) (h : n > 0) : ∑ k ∈ Finset.range (n + 1), (-1 : ℤ)^k * choose n k = 0 := by
  rw [Int.alternating_sum_range_choose, if_neg h.ne']

example : (∀ (n : ℕ) (h : n > 0), ∑ k ∈ Finset.range (n + 1), (-1 : ℤ)^k * choose n k = 0) := @solution
#print axioms solution

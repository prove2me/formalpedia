-- Prove2me | solution 1 for WorkbookSource.problem_18892
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:15:06.102472+00:00
-- url     : https://prove2.me/submissions/1a9d2a65-a19b-4292-8fdd-072b04887ebf

/- Source: InternLM Lean-Workbook lean_workbook_18892, Apache-2.0.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json -/
import Mathlib
open Nat Real
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (n : ℕ) : ∑ l ∈ (Finset.range n), 1 = n := by
  simp

example : (∀ (n : ℕ), ∑ l ∈ (Finset.range n), 1 = n) := @solution
#print axioms solution

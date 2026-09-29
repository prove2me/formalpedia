-- Prove2me | solution 1 for WorkbookSource.problem_18637
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:15:05.230008+00:00
-- url     : https://prove2.me/submissions/e9cf1e00-c4b0-47e6-aa6c-bcb4b219c47a

/- Source: InternLM Lean-Workbook lean_workbook_18637, Apache-2.0.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json -/
import Mathlib
open Nat Real
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (k : ℤ) : 1^3+k+2-1+k-2=0 ↔ k = 0 := by
  constructor <;> intro h <;> omega

example : (∀ (k : ℤ), 1^3+k+2-1+k-2=0 ↔ k = 0) := @solution
#print axioms solution

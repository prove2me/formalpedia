-- Prove2me | solution 1 for WorkbookSource.problem_15761
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:15:02.959159+00:00
-- url     : https://prove2.me/submissions/0237d713-67a1-4845-aabd-58b0543b0c9a

/- Source: InternLM Lean-Workbook lean_workbook_15761, Apache-2.0.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json -/
import Mathlib
open Nat Real
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution : ¬ (∃ n : ℤ, n^2 - 30*n + 236 ≤ 3) := by
  rintro ⟨n, hn⟩
  nlinarith [sq_nonneg (n-15)]

example : (¬ (∃ n : ℤ, n^2 - 30*n + 236 ≤ 3)) := @solution
#print axioms solution

-- Prove2me | solution 1 for WorkbookSource.problem_4689
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:14:58.401658+00:00
-- url     : https://prove2.me/submissions/263c01f0-c568-4eea-b710-79b33fe633f7

/- Source: InternLM Lean-Workbook lean_workbook_4689, Apache-2.0.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json -/
import Mathlib
open Nat Real
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution : ∀ n : ℤ, n^4 - 20*n^2 + 4 = (n^2 - 4*n - 2)*(n^2 + 4*n - 2) := by
  intro n
  ring

example : (∀ n : ℤ, n^4 - 20*n^2 + 4 = (n^2 - 4*n - 2)*(n^2 + 4*n - 2)) := @solution
#print axioms solution

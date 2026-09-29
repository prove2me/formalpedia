-- Prove2me | solution 1 for WorkbookSource.problem_7425
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:37:48.655984+00:00
-- url     : https://prove2.me/submissions/5dbb1e6c-7f0c-494f-a2bc-ad1f6d330ff2

/- Source: InternLM Lean-Workbook lean_workbook_7425, Apache-2.0.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json -/
import Mathlib
open Nat Real
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
theorem solution : Finset.card (Finset.filter (λ x => x % 7 = 2) (Finset.Icc 1000 2000)) = 143 := by
  decide

example : (Finset.card (Finset.filter (λ x => x % 7 = 2) (Finset.Icc 1000 2000)) = 143) := @solution
#print axioms solution

-- Prove2me | solution 1 for WorkbookSource.problem_3486
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:14:57.607472+00:00
-- url     : https://prove2.me/submissions/de8c87e4-60d0-4e7b-bf9d-238d119d5a6c

/- Source: InternLM Lean-Workbook lean_workbook_3486, Apache-2.0.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json -/
import Mathlib
open Nat Real
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (N : ℕ) : 991 + 993 + 995 + 997 + 999 = 5000 - N → N = 25 := by
  intro h
  omega

example : (∀ (N : ℕ), 991 + 993 + 995 + 997 + 999 = 5000 - N → N = 25) := @solution
#print axioms solution

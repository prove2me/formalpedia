-- Prove2me | solution 1 for WorkbookSource.problem_47286
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:40:44.54881+00:00
-- url     : https://prove2.me/submissions/cd3a152f-90ef-49ef-9edf-73de252e6696

/- Source: InternLM Lean-Workbook lean_workbook_47286, Apache-2.0.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json -/
import Mathlib
open Nat Real
open scoped Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 8192
set_option exponentiation.threshold 5000
theorem solution (a : ℕ) : 20 * 21 + 2021 = 2441 := by
  norm_num

example : (∀ (a : ℕ), 20 * 21 + 2021 = 2441) := @solution
#print axioms solution

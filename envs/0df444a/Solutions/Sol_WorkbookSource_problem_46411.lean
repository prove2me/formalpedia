-- Prove2me | solution 1 for WorkbookSource.problem_46411
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:40:43.692914+00:00
-- url     : https://prove2.me/submissions/97643a7d-7f01-406f-b3f6-563cfc462448

/- Source: InternLM Lean-Workbook lean_workbook_46411, Apache-2.0.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json -/
import Mathlib
open Nat Real
open scoped Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 8192
set_option exponentiation.threshold 5000
theorem solution (x : ℕ) (hx: x = 5) : √(96 * 98 - 71 * 73) = 65 := by
  norm_num

example : (∀ (x : ℕ) (hx: x = 5), √(96 * 98 - 71 * 73) = 65) := @solution
#print axioms solution

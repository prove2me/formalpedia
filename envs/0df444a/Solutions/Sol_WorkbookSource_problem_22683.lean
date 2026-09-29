-- Prove2me | solution 1 for WorkbookSource.problem_22683
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:40:30.042501+00:00
-- url     : https://prove2.me/submissions/928bc4eb-d584-4a64-bbf2-8f658e93e168

/- Source: InternLM Lean-Workbook lean_workbook_22683, Apache-2.0.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json -/
import Mathlib
open Nat Real
open scoped Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 8192
set_option exponentiation.threshold 5000
theorem solution : ∀ n : ℕ, (6 * 2002 ^ n) ^ 4 + (5 * 2002 ^ n) ^ 4 + (3 * 2002 ^ n) ^ 4 = 2002 ^ (4 * n + 1) := by
  intro n
  rw [show 4*n+1=n*4+1 by omega, pow_add, pow_one, pow_mul]
  ring

example : (∀ n : ℕ, (6 * 2002 ^ n) ^ 4 + (5 * 2002 ^ n) ^ 4 + (3 * 2002 ^ n) ^ 4 = 2002 ^ (4 * n + 1)) := @solution
#print axioms solution

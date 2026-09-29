-- Prove2me | solution 1 for WorkbookSource.problem_30147
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:40:36.137391+00:00
-- url     : https://prove2.me/submissions/f01fce4e-0bd8-4c0e-ba61-9aed9f4eebc0

/- Source: InternLM Lean-Workbook lean_workbook_30147, Apache-2.0.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json -/
import Mathlib
open Nat Real
open scoped Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 8192
set_option exponentiation.threshold 5000
theorem solution (p : ℕ) (hp : p ≡ 2 [ZMOD 5]) : 5 ∣ 2 * p + 1 := by
  simp only [Int.ModEq] at hp
  omega

example : (∀ (p : ℕ) (hp : p ≡ 2 [ZMOD 5]), 5 ∣ 2 * p + 1) := @solution
#print axioms solution

-- Prove2me | solution 1 for WorkbookSource.problem_30423
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:40:36.965898+00:00
-- url     : https://prove2.me/submissions/2701c9ae-f62e-487b-aba8-55f5222c91c1

/- Source: InternLM Lean-Workbook lean_workbook_30423, Apache-2.0.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json -/
import Mathlib
open Nat Real
open scoped Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 8192
set_option exponentiation.threshold 5000
theorem solution (x : ℕ) (hx : x < 24) : ¬ (x % 3 = 0 ∧ x % 8 = 0 ∧ x % 4 ≠ 0) := by
  rintro ⟨h3,h8,h4⟩
  omega

example : (∀ (x : ℕ) (hx : x < 24), ¬ (x % 3 = 0 ∧ x % 8 = 0 ∧ x % 4 ≠ 0)) := @solution
#print axioms solution

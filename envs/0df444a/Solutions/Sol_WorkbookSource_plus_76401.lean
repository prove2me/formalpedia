-- Prove2me | solution 1 for WorkbookSource.plus_76401
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:47:30.52619+00:00
-- url     : https://prove2.me/submissions/b714b272-3535-4051-9827-2977d22e339d

/- Source: InternLM Lean-Workbook lean_workbook_plus_76401, Apache-2.0.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json -/
import Mathlib
open Nat Real
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b n : ℕ) (h₀ : 1 ≤ a ∧ a ≤ 9) (h₁ : 0 ≤ b ∧ b ≤ 9) (h₂ : n = 10 * a + b) (h₃ : n = a * b + a + b) : b = 9 := by
  nlinarith [h₀.1, h₀.2, h₁.1, h₁.2]

example : (∀ (a b n : ℕ) (h₀ : 1 ≤ a ∧ a ≤ 9) (h₁ : 0 ≤ b ∧ b ≤ 9) (h₂ : n = 10 * a + b) (h₃ : n = a * b + a + b), b = 9) := @solution
#print axioms solution

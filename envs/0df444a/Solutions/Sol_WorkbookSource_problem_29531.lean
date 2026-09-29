-- Prove2me | solution 1 for WorkbookSource.problem_29531
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:40:34.318657+00:00
-- url     : https://prove2.me/submissions/cb40707e-8e91-46c5-8dd4-61d6b5d1ec05

/- Source: InternLM Lean-Workbook lean_workbook_29531, Apache-2.0.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json -/
import Mathlib
open Nat Real
open scoped Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 8192
set_option exponentiation.threshold 5000
theorem solution (f : ℤ → ℤ) (h₁ : ∀ x, f x = f (x - 1) + 4) (h₂ : f 0 = 3) : f (f (f 5)) = 383 := by
  have hf (n : ℕ) : f (n : ℤ) = 4 * n + 3 := by
    induction n with
    | zero => exact h₂
    | succ n ih =>
      have hs := h₁ ((n : ℤ)+1)
      norm_num at hs ⊢
      rw [hs, ih]
      ring
  have h5 := hf 5
  have h23 := hf 23
  have h95 := hf 95
  norm_num at h5 h23 h95
  rw [h5,h23,h95]

example : (∀ (f : ℤ → ℤ) (h₁ : ∀ x, f x = f (x - 1) + 4) (h₂ : f 0 = 3), f (f (f 5)) = 383) := @solution
#print axioms solution

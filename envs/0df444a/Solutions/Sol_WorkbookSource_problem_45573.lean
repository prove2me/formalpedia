-- Prove2me | solution 1 for WorkbookSource.problem_45573
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:40:42.794647+00:00
-- url     : https://prove2.me/submissions/86515618-e595-4146-9bda-29df881bba1e

/- Source: InternLM Lean-Workbook lean_workbook_45573, Apache-2.0.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json -/
import Mathlib
open Nat Real
open scoped Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 8192
set_option exponentiation.threshold 5000
theorem solution (f : ℕ → ℕ → ℕ) (x : ℕ) (n : ℕ)
  (h₀ : ∀ x, f x 0 = x)
  (h₁ : ∀ x n, f x (n + 1) = f (f x n) n) :
  f x n = x := by
  induction n with
  | zero => exact h₀ x
  | succ n ih => simpa [ih] using h₁ x n

example : (∀ (f : ℕ → ℕ → ℕ) (x : ℕ) (n : ℕ)
  (h₀ : ∀ x, f x 0 = x)
  (h₁ : ∀ x n, f x (n + 1) = f (f x n) n), f x n = x) := @solution
#print axioms solution

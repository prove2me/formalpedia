-- Prove2me | solution 1 for WorkbookSource.plus_6014
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:44:07.867247+00:00
-- url     : https://prove2.me/submissions/2522bec4-4e56-4d3e-acea-05fa0723f4e4

/- Source: InternLM Lean-Workbook lean_workbook_plus_6014, Apache-2.0.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json -/
import Mathlib
open Nat Real
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1000
theorem solution (a b : ℕ → ℝ) (h₁ : ∀ ε > 0, ∃ N, ∀ n ≥ N, |(3 * a n + 4 * b n) - 8| < ε) (h₂ : ∀ ε > 0, ∃ N, ∀ n ≥ N, |(6 * a n - b n) - 1| < ε) : ∀ ε > 0, ∃ N, ∀ n ≥ N, |(2 * a n - 5 * b n) - (-67 / 9)| < ε := by
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := h₁ (ε / 3) (by positivity)
  obtain ⟨N₂, hN₂⟩ := h₂ (ε / 3) (by positivity)
  use max N₁ N₂
  intro n hn
  have h₁' := hN₁ n (le_of_max_le_left hn)
  have h₂' := hN₂ n (le_of_max_le_right hn)
  simp only [abs_sub_lt_iff] at *
  constructor <;> linarith

example : (∀ (a b : ℕ → ℝ) (h₁ : ∀ ε > 0, ∃ N, ∀ n ≥ N, |(3 * a n + 4 * b n) - 8| < ε) (h₂ : ∀ ε > 0, ∃ N, ∀ n ≥ N, |(6 * a n - b n) - 1| < ε), ∀ ε > 0, ∃ N, ∀ n ≥ N, |(2 * a n - 5 * b n) - (-67 / 9)| < ε) := @solution
#print axioms solution

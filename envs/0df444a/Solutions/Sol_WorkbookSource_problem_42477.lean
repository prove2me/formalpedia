-- Prove2me | solution 1 for WorkbookSource.problem_42477
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:40:41.230475+00:00
-- url     : https://prove2.me/submissions/f7d2e7a8-646d-4ae6-b3de-1c9ed43bf965

/- Source: InternLM Lean-Workbook lean_workbook_42477, Apache-2.0.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json -/
import Mathlib
open Nat Real
open scoped Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 8192
set_option exponentiation.threshold 5000
theorem solution (u : ℕ → ℕ) (h1 : ∀ m n : ℕ, u (m * n) = u m * u n) (h2 : u 10 = 0) (h3 : ∀ k : ℕ, k % 10 = 3 → u k = 0) : u 2007 = 0 := by
  rw [show 2007 = 3 * 669 by norm_num, h1, h3 3 (by norm_num)]
  simp

example : (∀ (u : ℕ → ℕ) (h1 : ∀ m n : ℕ, u (m * n) = u m * u n) (h2 : u 10 = 0) (h3 : ∀ k : ℕ, k % 10 = 3 → u k = 0), u 2007 = 0) := @solution
#print axioms solution

-- Prove2me | solution 1 for WorkbookSource.plus_65242
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:47:29.584559+00:00
-- url     : https://prove2.me/submissions/6dec3775-0ed2-4a06-bc53-98dedc8e2cfd

/- Source: InternLM Lean-Workbook lean_workbook_plus_65242, Apache-2.0.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json -/
import Mathlib
open Nat Real
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (N : ℕ) (hN : 4 ≤ N) : (N % 2 = 0 ∧ ∃ m:ℕ, N = 2*m) ∨ (N % 2 = 1 ∧ ∃ m:ℕ, N = 2*m + 5) := by
  rcases Nat.mod_two_eq_zero_or_one N with h | h
  · exact Or.inl ⟨h, N/2, by omega⟩
  · exact Or.inr ⟨h, (N-5)/2, by omega⟩

example : (∀ (N : ℕ) (hN : 4 ≤ N), (N % 2 = 0 ∧ ∃ m:ℕ, N = 2*m) ∨ (N % 2 = 1 ∧ ∃ m:ℕ, N = 2*m + 5)) := @solution
#print axioms solution

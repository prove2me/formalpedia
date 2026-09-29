-- Prove2me | solution 1 for WorkbookSource.problem_5606
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:15:00.01081+00:00
-- url     : https://prove2.me/submissions/c108af95-8f1d-489c-a60e-63a40e23575a

/- Source: InternLM Lean-Workbook lean_workbook_5606, Apache-2.0.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json -/
import Mathlib
open Nat Real
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b n : ℕ) (hab : a = 4 ∧ b = 2) (hn : n = 3) : a^n - b^n = 56 := by
  rcases hab with ⟨rfl,rfl⟩
  subst n
  norm_num

example : (∀ (a b n : ℕ) (hab : a = 4 ∧ b = 2) (hn : n = 3), a^n - b^n = 56) := @solution
#print axioms solution

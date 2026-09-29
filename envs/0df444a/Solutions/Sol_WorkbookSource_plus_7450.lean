-- Prove2me | solution 1 for WorkbookSource.plus_7450
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:47:27.270189+00:00
-- url     : https://prove2.me/submissions/7e1eb590-3fde-44bf-bcdd-33050a9d269e

/- Source: InternLM Lean-Workbook lean_workbook_plus_7450, Apache-2.0.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json -/
import Mathlib
open Nat Real
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution : ¬ (∃ x : ℕ, x ≡ 4 [ZMOD 9] ∧ x ≡ 5 [ZMOD 12]) := by
  rintro ⟨x, hx₁, hx₂⟩
  simp only [Int.ModEq] at hx₁ hx₂
  omega

example : (¬ (∃ x : ℕ, x ≡ 4 [ZMOD 9] ∧ x ≡ 5 [ZMOD 12])) := @solution
#print axioms solution

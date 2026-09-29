-- Prove2me | solution 1 for WorkbookSource.problem_57161
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:47:26.434073+00:00
-- url     : https://prove2.me/submissions/6efd2280-b129-4b10-94b8-7df8cdb6aa35

/- Source: InternLM Lean-Workbook lean_workbook_57161, Apache-2.0.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json -/
import Mathlib
open Nat Real
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℤ) (h : 3 ∣ a + b + c) : 3 ∣ a^3 + b^3 + c^3 := by
  have h1 : a^3 + b^3 + c^3 = (a + b + c) * (a^2 - a * b + b^2 - a * c - b * c + c^2) + 3 * (a * b * c) := by ring
  rw [h1]
  obtain ⟨k, hk⟩ := h
  use k * (a^2 - a * b + b^2 - a * c - b * c + c^2) + a * b * c
  rw [hk]
  ring

example : (∀ (a b c : ℤ) (h : 3 ∣ a + b + c), 3 ∣ a^3 + b^3 + c^3) := @solution
#print axioms solution

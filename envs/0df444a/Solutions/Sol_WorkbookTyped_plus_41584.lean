-- Prove2me | solution 1 for WorkbookTyped.plus_41584
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:44:32.072139+00:00
-- url     : https://prove2.me/submissions/2dffedb3-be00-4f67-a449-9a0078dfeab6

/- Source: InternLM Lean-Workbook, lean_workbook_plus_41584. Apache-2.0.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json
This is an explicit-binder repair, not an unchanged formal declaration.
Added explicit integer binders (a b : ℤ), as required by the source wording. The malformed platform declaration has undeclared variables; its inferred natural-number interpretation is not retained. -/
import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000

theorem solution (a b : ℤ) : 29 ∣ (3 * a + 2 * b) ↔ 29 ∣ (11 * a + 17 * b) := by
  constructor <;> intro h <;> omega

example : (∀ (a b : ℤ), 29 ∣ (3 * a + 2 * b) ↔ 29 ∣ (11 * a + 17 * b)) := @solution
#print axioms solution

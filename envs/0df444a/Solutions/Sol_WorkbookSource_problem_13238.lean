-- Prove2me | solution 1 for WorkbookSource.problem_13238
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:15:02.036469+00:00
-- url     : https://prove2.me/submissions/cd6be8ad-965b-4266-8ba2-1d0da074f2a6

/- Source: InternLM Lean-Workbook lean_workbook_13238, Apache-2.0.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json -/
import Mathlib
open Nat Real
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution : ∃ x y : ℤ, (x^2 ≡ y^2 [ZMOD 3]) ∧ ¬ (x ≡ y [ZMOD 3]) := by
  exact ⟨1, 2, by decide, by decide⟩

example : (∃ x y : ℤ, (x^2 ≡ y^2 [ZMOD 3]) ∧ ¬ (x ≡ y [ZMOD 3])) := @solution
#print axioms solution

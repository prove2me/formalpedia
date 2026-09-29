-- Prove2me | solution 1 for WorkbookSource.plus_5958
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:44:07.146417+00:00
-- url     : https://prove2.me/submissions/51e52288-9519-4d93-9b69-bda92fc3001f

/- Source: InternLM Lean-Workbook lean_workbook_plus_5958, Apache-2.0.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json -/
import Mathlib
open Nat Real
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1000
theorem solution (a b c : ℝ) (h : a + b^2 + c^2 = 4) : a^2 + b^2 + c^2 ≥ 15 / 4 := by
  nlinarith [sq_nonneg (a-1/2)]

example : (∀ (a b c : ℝ) (h : a + b^2 + c^2 = 4), a^2 + b^2 + c^2 ≥ 15 / 4) := @solution
#print axioms solution

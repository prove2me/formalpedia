-- Prove2me | solution 1 for WorkbookSource.problem_57135
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:44:03.5411+00:00
-- url     : https://prove2.me/submissions/4f1d0d6c-8676-4e5b-b60f-f971c65ec5bd

/- Source: InternLM Lean-Workbook lean_workbook_57135, Apache-2.0.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json -/
import Mathlib
open Nat Real
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1000
theorem solution (a b c : ℝ) : (a + b + c) ^ 2 / (a ^ 2 + b ^ 2 + c ^ 2 + 3) ≤ 1 → a * b + b * c + c * a ≤ 3 / 2 := by
  intro h
  have hd : 0 < a^2+b^2+c^2+3 := by positivity
  have hh := (div_le_iff₀ hd).mp h
  nlinarith

example : (∀ (a b c : ℝ), (a + b + c) ^ 2 / (a ^ 2 + b ^ 2 + c ^ 2 + 3) ≤ 1 → a * b + b * c + c * a ≤ 3 / 2) := @solution
#print axioms solution

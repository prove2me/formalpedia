-- Prove2me | solution 1 for WorkbookSource.problem_26643
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:40:33.399362+00:00
-- url     : https://prove2.me/submissions/2e529af3-780d-4d3d-8996-b565b9c2a011

/- Source: InternLM Lean-Workbook lean_workbook_26643, Apache-2.0.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json -/
import Mathlib
open Nat Real
open scoped Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 8192
set_option exponentiation.threshold 5000
theorem solution (x : ℕ) (h : 2 * x + 5 = 17) : x = 6 := by
  omega

example : (∀ (x : ℕ) (h : 2 * x + 5 = 17), x = 6) := @solution
#print axioms solution

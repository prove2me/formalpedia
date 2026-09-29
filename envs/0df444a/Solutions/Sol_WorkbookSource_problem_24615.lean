-- Prove2me | solution 1 for WorkbookSource.problem_24615
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:40:30.937269+00:00
-- url     : https://prove2.me/submissions/c1a7ba0c-c890-4165-aba2-934762d2479b

/- Source: InternLM Lean-Workbook lean_workbook_24615, Apache-2.0.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json -/
import Mathlib
open Nat Real
open scoped Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 8192
set_option exponentiation.threshold 5000
theorem solution (p : ℕ) (hp : p = 5) : 2^(p-1) * (2^p - 1) = 496 := by
  norm_num [hp]

example : (∀ (p : ℕ) (hp : p = 5), 2^(p-1) * (2^p - 1) = 496) := @solution
#print axioms solution

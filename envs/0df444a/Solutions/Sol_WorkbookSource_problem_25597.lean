-- Prove2me | solution 1 for WorkbookSource.problem_25597
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:40:32.593315+00:00
-- url     : https://prove2.me/submissions/4da9851c-6c01-481b-b5e5-aa67083e9971

/- Source: InternLM Lean-Workbook lean_workbook_25597, Apache-2.0.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json -/
import Mathlib
open Nat Real
open scoped Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 8192
set_option exponentiation.threshold 5000
theorem solution (h : 3 ≤ 2014) : (Nat.choose 2014 3 : ℕ) = 1359502364 := by
  have hh := Nat.add_one_mul_choose_eq 2013 2
  norm_num [Nat.choose_two_right] at hh
  omega

example : (∀ (h : 3 ≤ 2014), (Nat.choose 2014 3 : ℕ) = 1359502364) := @solution
#print axioms solution

-- Prove2me | solution 1 for WorkbookSource.problem_7649
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:37:49.576857+00:00
-- url     : https://prove2.me/submissions/a1d8d646-b1ab-4c91-b207-88fa57a71863

/- Source: InternLM Lean-Workbook lean_workbook_7649, Apache-2.0.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json -/
import Mathlib
open Nat Real
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
theorem solution : ∑ k ∈ Finset.filter (λ x => ¬ (4 ∣ x ∨ 7 ∣ x)) (Finset.range 100), 1 = 64 := by
  norm_num only [Finset.sum_const, smul_eq_mul, mul_one]
  decide

example : (∑ k ∈ Finset.filter (λ x => ¬ (4 ∣ x ∨ 7 ∣ x)) (Finset.range 100), 1 = 64) := @solution
#print axioms solution

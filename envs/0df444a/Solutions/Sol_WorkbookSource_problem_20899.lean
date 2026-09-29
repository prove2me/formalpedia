-- Prove2me | solution 1 for WorkbookSource.problem_20899
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:37:50.930146+00:00
-- url     : https://prove2.me/submissions/bb89c20e-8116-4407-acb2-cebde4212953

/- Source: InternLM Lean-Workbook lean_workbook_20899, Apache-2.0.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json -/
import Mathlib
open Nat Real
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
theorem solution : ∑ i ∈ Finset.filter (λ x => ¬ (5∣x) ∧ ¬ (7∣x)) (Finset.Icc 1 2006), 1 = 1376 := by
  norm_num only [Finset.sum_const, smul_eq_mul, mul_one]
  decide

example : (∑ i ∈ Finset.filter (λ x => ¬ (5∣x) ∧ ¬ (7∣x)) (Finset.Icc 1 2006), 1 = 1376) := @solution
#print axioms solution

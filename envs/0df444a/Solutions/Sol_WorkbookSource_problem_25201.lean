-- Prove2me | solution 1 for WorkbookSource.problem_25201
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:41:54.515513+00:00
-- url     : https://prove2.me/submissions/c1be15e4-8035-4f07-a243-07cf5c7f8f29

/- Source: InternLM Lean-Workbook, record lean_workbook_25201.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json
Apache-2.0. Complete original proposition preserved; source candidate proof adapted only for Mathlib compatibility where documented. -/
import Mathlib
open Real
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem solution (x y : ℝ) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (hpq : p + q < 1) : (p * x + q * y) ^ 2 ≤ p * x ^ 2 + q * y ^ 2 := by
  first
  | solve
    | have : 0 ≤ p * (x - y) ^ 2 := by positivity
      nlinarith
  | solve
    | have h2 : 0 ≤ p * (x - y) ^ 2 := by nlinarith
      nlinarith
  | solve
    | have : 0 ≤ p * q := mul_nonneg hp.le hq.le
      nlinarith [sq_nonneg (x - y)]
  | solve
    | have h2 : 0 ≤ p * q := mul_nonneg hp.le hq.le
      nlinarith [sq_nonneg (x - y)]
  | solve
    | rw [sq, sq, sq]
      have h1 : 0 ≤ p * (x - y) ^ 2 := by nlinarith
      have h2 : 0 ≤ q * (x - y) ^ 2 := by nlinarith
      nlinarith

example : (∀ (x y : ℝ) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (hpq : p + q < 1), (p * x + q * y) ^ 2 ≤ p * x ^ 2 + q * y ^ 2) := @solution
#print axioms solution

-- Prove2me | solution 1 for WorkbookSource.problem_26366
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:41:55.298889+00:00
-- url     : https://prove2.me/submissions/52a2fcba-4e44-4f91-9e78-967ebbb8ef54

/- Source: InternLM Lean-Workbook, record lean_workbook_26366.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json
Apache-2.0. Complete original proposition preserved; source candidate proof adapted only for Mathlib compatibility where documented. -/
import Mathlib
open Real
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem solution (x y a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (a * x + b * y) * (b * x + a * y) ≥ (a + b) ^ 2 * x * y := by
  first
  | solve
    | nlinarith [sq_nonneg (b * x + a * y - (a + b) * y), ha, hb]
  | solve
    | nlinarith [sq_nonneg (a * x + b * y - (a + b) * y), sq_nonneg (b * x + a * y - (a + b) * x)]
  | solve
    | rw [sq]
      nlinarith [sq_nonneg (a * x + b * y - (a + b) * y), sq_nonneg (a * y + b * x - (a + b) * x)]
  | solve
    | ring_nf
      nlinarith [sq_nonneg (a * x + b * y - (a + b) * y), sq_nonneg (b * x + a * y - (a + b) * x)]
  | solve
    | have h1 : 0 ≤ (a * b) * (x - y) ^ 2 := mul_nonneg (mul_nonneg ha.le hb.le) (sq_nonneg (x - y))
      linarith
  | solve
    | ring_nf
      have : 0 ≤ (a * b) * (x - y) ^ 2 := mul_nonneg (mul_nonneg ha.le hb.le) (sq_nonneg (x - y))
      linarith

example : (∀ (x y a b : ℝ) (ha : 0 < a) (hb : 0 < b), (a * x + b * y) * (b * x + a * y) ≥ (a + b) ^ 2 * x * y) := @solution
#print axioms solution

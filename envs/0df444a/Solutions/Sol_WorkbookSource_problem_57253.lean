-- Prove2me | solution 1 for WorkbookSource.problem_57253
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T13:06:45.103457+00:00
-- url     : https://prove2.me/submissions/b557bac2-4c0e-4512-9890-e2480b00b20c

/- Source: InternLM Lean-Workbook, record lean_workbook_57253.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json
Apache-2.0. Complete original proposition preserved. Proof compatibility changes, if any, are documented in the explanation. -/
import Mathlib
open Real
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem solution (a b c : ℝ) (habc : a + b + c = 1) (h : a > 0 ∧ b > 0 ∧ c > 0) : a * b + b * c + c * a > 2 * a * b * c := by
  first
  | solve
    | nlinarith [mul_nonneg h.1.le h.2.1.le, mul_nonneg h.1.le h.2.2.le, mul_nonneg h.2.1.le h.2.2.le]
  | solve
    | nlinarith [mul_nonneg h.1.le h.2.1.le, mul_nonneg h.2.1.le h.2.2.le, mul_nonneg h.2.2.le h.1.le]

example : (∀ (a b c : ℝ) (habc : a + b + c = 1) (h : a > 0 ∧ b > 0 ∧ c > 0), a * b + b * c + c * a > 2 * a * b * c) := @solution
#print axioms solution

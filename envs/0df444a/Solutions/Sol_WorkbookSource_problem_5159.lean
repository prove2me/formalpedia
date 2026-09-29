-- Prove2me | solution 1 for WorkbookSource.problem_5159
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:17:44.236237+00:00
-- url     : https://prove2.me/submissions/9c0bb67c-f30c-42d7-b0e8-6644ab6e1dd3

/- Source: InternLM Lean-Workbook, record lean_workbook_5159.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json
Apache-2.0. Original statement and candidate proofs preserved. -/
import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem solution (a b c: ℝ) (hab : a * b + a * c + b * c = 3) : a ^ 2 + b ^ 2 + c ^ 2 + 5 * (a * b + b * c + c * a) ≥ 6 * (a + b + c) := by
  first
  | solve
    | have h1 := sq_nonneg (a + b + c - 3)
      linarith
  | solve
    | have h1 := sq_nonneg (a + b + c - 3)
      linarith [hab]
  | solve
    | have h0 := sq_nonneg (a + b + c - 3)
      linarith [hab]
  | solve
    | rw [add_comm]
      nlinarith [sq_nonneg (a + b + c - 3)]
  | solve
    | ring_nf at hab ⊢
      nlinarith [sq_nonneg (a + b + c - 3)]
  | solve
    | nlinarith [sq_nonneg (a + b + c - 3), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]

example : (∀ (a b c: ℝ) (hab : a * b + a * c + b * c = 3), a ^ 2 + b ^ 2 + c ^ 2 + 5 * (a * b + b * c + c * a) ≥ 6 * (a + b + c)) := @solution
#print axioms solution

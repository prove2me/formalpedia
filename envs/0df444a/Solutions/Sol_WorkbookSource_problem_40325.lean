-- Prove2me | solution 1 for WorkbookSource.problem_40325
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T13:06:32.196506+00:00
-- url     : https://prove2.me/submissions/9af1109a-88ce-4f21-8d6b-970ef9086081

/- Source: InternLM Lean-Workbook, record lean_workbook_40325.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json
Apache-2.0. Complete original proposition preserved. Proof compatibility changes, if any, are documented in the explanation. -/
import Mathlib
open Real
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem solution (r : ℕ → ℝ) : 2 * (r 1 ^ 2 + r 2 ^ 2 + r 3 ^ 2 + r 4 ^ 2 + r 5 ^ 2) ≥ r 1 * r 2 + r 1 * r 3 + r 1 * r 4 + r 1 * r 5 + r 2 * r 3 + r 2 * r 4 + r 2 * r 5 + r 3 * r 4 + r 3 * r 5 + r 4 * r 5 := by
  first
  | solve
    | have : 0 ≤ (r 1 - r 2) ^ 2 + (r 1 - r 3) ^ 2 + (r 1 - r 4) ^ 2 + (r 1 - r 5) ^ 2 + (r 2 - r 3) ^ 2 + (r 2 - r 4) ^ 2 + (r 2 - r 5) ^ 2 + (r 3 - r 4) ^ 2 + (r 3 - r 5) ^ 2 + (r 4 - r 5) ^ 2 := by positivity
      linarith
  | solve
    | linarith [sq_nonneg (r 1 - r 2), sq_nonneg (r 1 - r 3), sq_nonneg (r 1 - r 4), sq_nonneg (r 1 - r 5),
        sq_nonneg (r 2 - r 3), sq_nonneg (r 2 - r 4), sq_nonneg (r 2 - r 5), sq_nonneg (r 3 - r 4),
        sq_nonneg (r 3 - r 5), sq_nonneg (r 4 - r 5)]
  | solve
    | have := sq_nonneg (r 1 - r 2)
      linarith [sq_nonneg (r 1 - r 3), sq_nonneg (r 1 - r 4), sq_nonneg (r 1 - r 5),
          sq_nonneg (r 2 - r 3), sq_nonneg (r 2 - r 4), sq_nonneg (r 2 - r 5),
          sq_nonneg (r 3 - r 4), sq_nonneg (r 3 - r 5), sq_nonneg (r 4 - r 5)]
  | solve
    | field_simp [mul_add, add_mul]
      ring_nf
      linarith [sq_nonneg (r 1 - r 2), sq_nonneg (r 1 - r 3), sq_nonneg (r 1 - r 4), sq_nonneg (r 1 - r 5), sq_nonneg (r 2 - r 3), sq_nonneg (r 2 - r 4), sq_nonneg (r 2 - r 5), sq_nonneg (r 3 - r 4), sq_nonneg (r 3 - r 5), sq_nonneg (r 4 - r 5)]
  | solve
    | simp [mul_comm, mul_assoc, mul_left_comm]
      linarith [sq_nonneg (r 1 - r 2), sq_nonneg (r 1 - r 3), sq_nonneg (r 1 - r 4), sq_nonneg (r 1 - r 5), sq_nonneg (r 2 - r 3), sq_nonneg (r 2 - r 4), sq_nonneg (r 2 - r 5), sq_nonneg (r 3 - r 4), sq_nonneg (r 3 - r 5), sq_nonneg (r 4 - r 5)]

example : (∀ (r : ℕ → ℝ), 2 * (r 1 ^ 2 + r 2 ^ 2 + r 3 ^ 2 + r 4 ^ 2 + r 5 ^ 2) ≥ r 1 * r 2 + r 1 * r 3 + r 1 * r 4 + r 1 * r 5 + r 2 * r 3 + r 2 * r 4 + r 2 * r 5 + r 3 * r 4 + r 3 * r 5 + r 4 * r 5) := @solution
#print axioms solution

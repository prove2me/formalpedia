-- Prove2me | solution 1 for WorkbookSource.problem_190
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:17:43.497068+00:00
-- url     : https://prove2.me/submissions/0f0e5bfb-d86a-4bb5-bcdc-4c4d3bf86334

/- Source: InternLM Lean-Workbook, record lean_workbook_190.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json
Apache-2.0. Original statement and candidate proofs preserved. -/
import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem solution (x y z : ℝ) (hx : x ∈ Set.Icc 0 1) (hy : y ∈ Set.Icc 0 1) (hxy : x + y ≤ 1) (hz : z ≥ 1) : 8 * x ^ 2 * y ^ 2 + z * (x + y) ^ 2 ≥ 4 * x * y * z := by
  first
  | solve
    | have : 0 ≤ (x - y) ^ 2 := sq_nonneg (x - y)
      nlinarith [hz, hxy]
  | solve
    | have h1 := sq_nonneg (x + y)
      have h2 := sq_nonneg (x - y)
      nlinarith
  | solve
    | have h1 : 0 ≤ (x - y) ^ 2 := sq_nonneg (x - y)
      nlinarith [hxy, hz, h1]
  | solve
    | have h1 : 0 ≤ (x - y) ^ 2 := sq_nonneg (x - y)
      nlinarith [hx.1, hx.2, hy.1, hy.2, hxy, hz, h1]

example : (∀ (x y z : ℝ) (hx : x ∈ Set.Icc 0 1) (hy : y ∈ Set.Icc 0 1) (hxy : x + y ≤ 1) (hz : z ≥ 1), 8 * x ^ 2 * y ^ 2 + z * (x + y) ^ 2 ≥ 4 * x * y * z) := @solution
#print axioms solution

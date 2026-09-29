-- Prove2me | solution 1 for WorkbookSource.problem_12814
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:17:46.074619+00:00
-- url     : https://prove2.me/submissions/32dd8e24-5462-4a2b-bc55-dc9d2244cd57

/- Source: InternLM Lean-Workbook, record lean_workbook_12814.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json
Apache-2.0. Original statement and candidate proofs preserved. -/
import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem solution (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x + y = 1) : x^2 + y^2 + x^2 * y^2 ≥ 9 / 16 := by
  first
  | solve
    | have : y = 1 - x := by linarith
      subst this
      ring_nf
      nlinarith [sq_nonneg (x - 1 / 2)]

example : (∀ (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x + y = 1), x^2 + y^2 + x^2 * y^2 ≥ 9 / 16) := @solution
#print axioms solution

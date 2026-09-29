-- Prove2me | solution 1 for WorkbookSource.plus_30537
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T13:06:46.495986+00:00
-- url     : https://prove2.me/submissions/586047ad-9fee-4d50-95b2-19b4d8b0fd8f

/- Source: InternLM Lean-Workbook, record lean_workbook_plus_30537.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json
Apache-2.0. Complete original proposition preserved. Proof compatibility changes, if any, are documented in the explanation. -/
import Mathlib
open Real
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem solution : ∀ a b c : ℝ, (b - a) ^ 2 + (c - b) ^ 2 + (c - a - 2) ^ 2 ≥ 4 / 3 := by
  first
  | solve
    | intros a b c
      field_simp [sq]
      ring_nf
      nlinarith [sq_nonneg (3 * b - 3 * a - 2), sq_nonneg (3 * c - 3 * b - 2)]

example : (∀ a b c : ℝ, (b - a) ^ 2 + (c - b) ^ 2 + (c - a - 2) ^ 2 ≥ 4 / 3) := @solution
#print axioms solution

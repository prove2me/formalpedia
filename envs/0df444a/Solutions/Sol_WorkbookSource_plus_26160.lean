-- Prove2me | solution 1 for WorkbookSource.plus_26160
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T13:06:45.811821+00:00
-- url     : https://prove2.me/submissions/d3f56da8-c0c6-4bf7-b051-bb0b4fc9ef2f

/- Source: InternLM Lean-Workbook, record lean_workbook_plus_26160.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json
Apache-2.0. Complete original proposition preserved. Proof compatibility changes, if any, are documented in the explanation. -/
import Mathlib
open Real
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b + a * b = 1) : (1 + b ^ 2) / (1 + a ^ 2) ≥ 2 * b := by
  rw [ge_iff_le, le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (1 - b), ha, hb, hab]

example : (∀ (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b + a * b = 1), (1 + b ^ 2) / (1 + a ^ 2) ≥ 2 * b) := @solution
#print axioms solution

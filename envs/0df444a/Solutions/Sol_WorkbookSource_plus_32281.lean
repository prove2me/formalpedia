-- Prove2me | solution 1 for WorkbookSource.plus_32281
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T13:16:31.245808+00:00
-- url     : https://prove2.me/submissions/f607a779-2746-4075-8199-7cb1f97e342d

/- Source: InternLM Lean-Workbook, record lean_workbook_plus_32281.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json
Apache-2.0. Complete original proposition and source candidate proof preserved. -/
import Mathlib
open Real
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem solution (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a + b + c = 1) : a^2 + b^2 + c^2 + 4 * a * b * c ≤ 1 := by
  first
  | solve
    | have : a = 1 - b - c := by linarith
      subst this
      nlinarith [ha, hb, hc]

example : (∀ (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a + b + c = 1), a^2 + b^2 + c^2 + 4 * a * b * c ≤ 1) := @solution
#print axioms solution

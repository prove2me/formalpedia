-- Prove2me | solution 1 for WorkbookSource.plus_62267
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T13:16:35.189253+00:00
-- url     : https://prove2.me/submissions/50504eb9-c712-4348-8e88-b551edf2885e

/- Source: InternLM Lean-Workbook, record lean_workbook_plus_62267.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json
Apache-2.0. Complete original proposition and source candidate proof preserved. -/
import Mathlib
open Real
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : 2*a^2 + 8*b^2 + 5*c^2 ≥ 4*a*b + 4*a*c + 4*b*c := by
  first
  | solve
    | have : 0 ≤ (a - 2 * b)^2 + (a - 2 * c)^2 + (2 * b - c)^2 := by nlinarith
      linarith [ha, hb, hc]
  | solve
    | have : (a - 2 * b)^2 + (a - 2 * c)^2 + (2 * b - c)^2 ≥ 0 := by positivity
      linarith [ha, hb, hc]
  | solve
    | have h1 : 0 ≤ (a - 2*b)^2 + (a - 2*c)^2 + (2*b - c)^2 := by positivity
      linarith [ha, hb, hc, h1]

example : (∀ (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0), 2*a^2 + 8*b^2 + 5*c^2 ≥ 4*a*b + 4*a*c + 4*b*c) := @solution
#print axioms solution

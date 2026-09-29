-- Prove2me | solution 1 for WorkbookSource.problem_48767
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T13:06:36.63119+00:00
-- url     : https://prove2.me/submissions/8fcd6550-768f-4709-a7a6-c189f248a3e8

/- Source: InternLM Lean-Workbook, record lean_workbook_48767.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json
Apache-2.0. Complete original proposition preserved. Proof compatibility changes, if any, are documented in the explanation. -/
import Mathlib
open Real
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem solution : ∀ a b c : ℝ, a^4 + b^4 + c^4 - a^3 * b - b^3 * c - c^3 * a = (a^2 + b^2 + a * b) * (a - b)^2 + (b^2 + b * c + c^2) * (a - c) * (b - c) := by
  first
  | solve
    | intro a b c
      ring
  | solve
    | intro x y z
      ring
  | solve
    | intros a b c
      ring
  | solve
    | rintro a b c
      ring
  | solve
    | rintro a b c
      ring_nf
  | solve
    | intro a b c
      linarith

example : (∀ a b c : ℝ, a^4 + b^4 + c^4 - a^3 * b - b^3 * c - c^3 * a = (a^2 + b^2 + a * b) * (a - b)^2 + (b^2 + b * c + c^2) * (a - c) * (b - c)) := @solution
#print axioms solution

-- Prove2me | solution 1 for WorkbookSource.problem_17980
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:41:48.576561+00:00
-- url     : https://prove2.me/submissions/98b04707-265f-4e53-8277-a5d3fbd660fe

/- Source: InternLM Lean-Workbook, record lean_workbook_17980.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json
Apache-2.0. Complete original proposition preserved; source candidate proof adapted only for Mathlib compatibility where documented. -/
import Mathlib
open Real
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem solution : ∀ t : ℝ, t > 2 → t * (t ^ 2 - 3) > 2 := by
  first
  | solve
    | intro t h
      nlinarith
  | solve
    | intro t ht
      nlinarith
  | solve
    | intros t ht2
      nlinarith
  | solve
    | intro t h
      nlinarith only [h]
  | solve
    | exact fun t ht ↦ by nlinarith
  | solve
    | intros t h
      nlinarith only [h]

example : (∀ t : ℝ, t > 2 → t * (t ^ 2 - 3) > 2) := @solution
#print axioms solution

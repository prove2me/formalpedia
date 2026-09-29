-- Prove2me | solution 1 for WorkbookSource.problem_36537
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:44:31.317085+00:00
-- url     : https://prove2.me/submissions/281d40b8-74b9-45e9-a7d0-4ec638a70ad0

/- Source: InternLM Lean-Workbook, record lean_workbook_36537.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json
Apache-2.0. Complete original proposition preserved; source candidate proof adapted only for Mathlib compatibility where documented. -/
import Mathlib
open Real
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem solution (β θ : ℝ) : (sin β + cos θ + 1)^2 ≥ 2 * (sin β + 1) * (cos θ + 1) → sin β ^ 2 ≥ sin θ ^ 2 := by
  first
  | solve
    | intro h
      nlinarith [sin_sq_add_cos_sq β, sin_sq_add_cos_sq θ]
  | solve
    | intro h
      linarith [h, sin_sq_add_cos_sq β, sin_sq_add_cos_sq θ]
  | solve
    | contrapose!
      intro h
      nlinarith [h, sin_sq_add_cos_sq β, sin_sq_add_cos_sq θ]

example : (∀ (β θ : ℝ), (sin β + cos θ + 1)^2 ≥ 2 * (sin β + 1) * (cos θ + 1) → sin β ^ 2 ≥ sin θ ^ 2) := @solution
#print axioms solution

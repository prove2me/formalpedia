-- Prove2me | solution 1 for WorkbookSource.problem_29382
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:44:23.689794+00:00
-- url     : https://prove2.me/submissions/676bc48e-2d0e-45fd-8542-499d071ce1ee

/- Source: InternLM Lean-Workbook, record lean_workbook_29382.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json
Apache-2.0. Complete original proposition preserved; source candidate proof adapted only for Mathlib compatibility where documented. -/
import Mathlib
open Real
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem solution (x : ℝ) (hx : 0 < x) : x + 2022 ≠ ⌊x⌋ * (x - ⌊x⌋) := by
  first
  | solve
    | nlinarith [hx, Int.floor_le x, Int.lt_floor_add_one x]
  | solve
    | intro h
      have h1 := Int.floor_le x
      have h2 := Int.lt_floor_add_one x
      nlinarith [h, h1, h2]
  | solve
    | by_contra h
      have h1 := Int.floor_le x
      have h2 := Int.lt_floor_add_one x
      contrapose! h
      nlinarith [h, h1, h2]

example : (∀ (x : ℝ) (hx : 0 < x), x + 2022 ≠ ⌊x⌋ * (x - ⌊x⌋)) := @solution
#print axioms solution

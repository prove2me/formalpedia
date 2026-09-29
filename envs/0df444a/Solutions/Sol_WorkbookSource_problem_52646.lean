-- Prove2me | solution 1 for WorkbookSource.problem_52646
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T13:06:40.452687+00:00
-- url     : https://prove2.me/submissions/087c5689-d843-4e39-b1d6-a9cf04e6977a

/- Source: InternLM Lean-Workbook, record lean_workbook_52646.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json
Apache-2.0. Complete original proposition preserved. Proof compatibility changes, if any, are documented in the explanation. -/
import Mathlib
open Real
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem solution (x y : ℝ) (hx : x ≥ 1) (hy : y ≥ 1) (hxy : x + y = 3) : (y^2 + y + 1) * (x + 1) + (x^2 - x - 1) * (y - 1) ≥ 9 := by
  first
  | solve
    | have : x = 3 - y := by linarith only [hxy]
      subst this
      nlinarith [hx, hy, hxy]

example : (∀ (x y : ℝ) (hx : x ≥ 1) (hy : y ≥ 1) (hxy : x + y = 3), (y^2 + y + 1) * (x + 1) + (x^2 - x - 1) * (y - 1) ≥ 9) := @solution
#print axioms solution

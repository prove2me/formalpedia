-- Prove2me | solution 1 for WorkbookSource.problem_5422
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:41:09.784584+00:00
-- url     : https://prove2.me/submissions/0f218f6d-5730-486d-9123-6c451bbec4c1

/- InternLM Lean-Workbook, lean_workbook_5422, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution : (1 / 2 : ℚ) * (1 / 2) * (1 / 4) = (1 / 16)  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | ring_nf at *
  | solve
    | norm_num at *
  | solve
    | field_simp; ring
  | solve
    | field_simp <;> ring
example : ((1 / 2 : ℚ) * (1 / 2) * (1 / 4) = (1 / 16)) := @solution
#print axioms solution

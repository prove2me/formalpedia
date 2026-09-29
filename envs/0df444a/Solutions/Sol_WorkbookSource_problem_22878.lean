-- Prove2me | solution 1 for WorkbookSource.problem_22878
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:52:05.697682+00:00
-- url     : https://prove2.me/submissions/e1e8571c-ccf2-4c22-9616-1194b0f1c871

/- InternLM Lean-Workbook, lean_workbook_22878, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution : (choose 24 5) - (choose 20 5) = 27000  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | congr 1
  | solve
    | norm_num [Nat.choose]
  | solve
    | rw [← Nat.cast_eq_ofNat]
      congr
  | solve
    | norm_num [Nat.choose, Nat.factorial]
example : ((choose 24 5) - (choose 20 5) = 27000) := @solution
#print axioms solution

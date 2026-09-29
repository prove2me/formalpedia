-- Prove2me | solution 1 for WorkbookSource.problem_10893
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:50:21.806737+00:00
-- url     : https://prove2.me/submissions/72f7232f-c565-43e6-bffb-8d2e66c5985e

/- InternLM Lean-Workbook, lean_workbook_10893, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution : 10112369 - 10113459 = -1090  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | ring_nf at *
  | solve
    | norm_num [Int.ofNat_add]
  | solve
    | simp [Int.sub_eq_add_neg]
  | solve
    | simp [Nat.sub_eq_zero_of_le]
example : (10112369 - 10113459 = -1090) := @solution
#print axioms solution

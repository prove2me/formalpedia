-- Prove2me | solution 1 for WorkbookSource.problem_29624
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:59:16.7081+00:00
-- url     : https://prove2.me/submissions/5f067652-3619-445f-9959-32657141293c

/- InternLM Lean-Workbook, lean_workbook_29624, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution : 3 ∣ 111  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | norm_num [dvd_def]
  | solve
    | ring_nf
      exact ⟨37, by ring⟩
  | solve
    | norm_num [Nat.mod_eq_of_lt]
  | solve
    | exact (by norm_num : 3 ∣ 111)
example : (3 ∣ 111) := @solution
#print axioms solution

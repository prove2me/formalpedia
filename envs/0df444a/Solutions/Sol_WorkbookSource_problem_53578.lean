-- Prove2me | solution 1 for WorkbookSource.problem_53578
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:10:09.747331+00:00
-- url     : https://prove2.me/submissions/8f123d67-aa02-44e6-ae72-c51076fe0ead

/- InternLM Lean-Workbook, lean_workbook_53578, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution : (2014 * 2015 * 4029) / 6 + (3 * 2014 * 2015) / 2 ≡ 5330 [MOD 10^4]  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | norm_num [ModEq]
  | solve
    | simp [Nat.ModEq]
  | solve
    | rw [ModEq]
      norm_num
  | solve
    | simp only [ModEq]
      ring_nf
example : ((2014 * 2015 * 4029) / 6 + (3 * 2014 * 2015) / 2 ≡ 5330 [MOD 10^4]) := @solution
#print axioms solution

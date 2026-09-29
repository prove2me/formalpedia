-- Prove2me | solution 1 for WorkbookSource.problem_21347
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:52:01.590179+00:00
-- url     : https://prove2.me/submissions/1ea461cd-c65a-44ff-9bfb-0cd99ed596d9

/- InternLM Lean-Workbook, lean_workbook_21347, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution : 2^(147) - 1 ≡ 0 [ZMOD 343]  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | conv_lhs => norm_num
  | solve
    | norm_num [Int.ModEq]
  | solve
    | rw [Int.ModEq]
      norm_num
  | solve
    | conv in 2^(147) => norm_num
example : (2^(147) - 1 ≡ 0 [ZMOD 343]) := @solution
#print axioms solution

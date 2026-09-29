-- Prove2me | solution 1 for WorkbookSource.problem_15540
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:39:34.950979+00:00
-- url     : https://prove2.me/submissions/ab788152-212d-44f1-aa09-744cb8d3ace8

/- InternLM Lean-Workbook, lean_workbook_15540, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution : (2^3 ≡ 1 [MOD 7]) ∧ (2^348 ≡ 1 [MOD 7]) ∧ (2^349 ≡ 2 [MOD 7])  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | norm_num [Nat.ModEq]
  | solve
    | refine ⟨?_,?_,?_⟩ <;> rfl
  | solve
    | simp only [ModEq]
      norm_num
  | solve
    | constructor
      all_goals decide
example : ((2^3 ≡ 1 [MOD 7]) ∧ (2^348 ≡ 1 [MOD 7]) ∧ (2^349 ≡ 2 [MOD 7])) := @solution
#print axioms solution

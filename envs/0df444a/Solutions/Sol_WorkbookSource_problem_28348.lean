-- Prove2me | solution 1 for WorkbookSource.problem_28348
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:17:46.825986+00:00
-- url     : https://prove2.me/submissions/ab84e629-14a3-4f6d-bf0b-d2106125af11

/- InternLM Lean-Workbook, lean_workbook_28348, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (x y : ℝ) : Continuous fun p : ℝ × ℝ => sin (p.1^2 + p.2^2)  := by
  first
  | solve
    | fun_prop
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | apply Real.continuous_sin.comp
      exact (continuous_fst.pow 2).add (continuous_snd.pow 2)
  | solve
    | apply continuous_sin.comp
      apply Continuous.add
      exact continuous_fst.pow 2
      apply Continuous.pow
      exact continuous_snd
example : (∀ (x y : ℝ), Continuous fun p : ℝ × ℝ => sin (p.1^2 + p.2^2)) := @solution
#print axioms solution

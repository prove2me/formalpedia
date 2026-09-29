-- Prove2me | solution 1 for WorkbookSource.problem_48897
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:09:52.854822+00:00
-- url     : https://prove2.me/submissions/c5f2c295-7d74-4fe4-bde1-7b90ab042be1

/- InternLM Lean-Workbook, lean_workbook_48897, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (a b c : ℝ) (habc : a + b + c > 0) : ¬ (a < 0 ∧ b < 0 ∧ c < 0)  := by
  rintro ⟨ha, hb, hc⟩
  linarith

example : (∀ (a b c : ℝ) (habc : a + b + c > 0), ¬ (a < 0 ∧ b < 0 ∧ c < 0)) := @solution
#print axioms solution

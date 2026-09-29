-- Prove2me | solution 1 for WorkbookSource.problem_47673
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T13:06:35.250328+00:00
-- url     : https://prove2.me/submissions/5b910a58-6961-47d2-8d78-d2d4e9dbcb41

/- Source: InternLM Lean-Workbook, record lean_workbook_47673.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json
Apache-2.0. Complete original proposition preserved. Proof compatibility changes, if any, are documented in the explanation. -/
import Mathlib
open Real
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem solution (a b: ℝ) (ha : 0 <= a ∧ a <= 1) (hb : 0 <= b ∧ b <= 1): a + (b - a*b) >= a ∧ a >= 0 := by
  first
  | solve
    | refine' ⟨_, ha.1⟩
      nlinarith
  | solve
    | constructor
      nlinarith
      exact ha.left
  | solve
    | constructor
      nlinarith
      simp [ha.left]
  | solve
    | constructor
      nlinarith
      linarith [ha.1]
  | solve
    | apply And.intro
      nlinarith
      linarith [ha.left]
  | solve
    | constructor
      nlinarith [ha, hb]
      linarith [ha.1]

example : (∀ (a b: ℝ) (ha : 0 <= a ∧ a <= 1) (hb : 0 <= b ∧ b <= 1), a + (b - a*b) >= a ∧ a >= 0) := @solution
#print axioms solution

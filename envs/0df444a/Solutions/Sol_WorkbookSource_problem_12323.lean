-- Prove2me | solution 1 for WorkbookSource.problem_12323
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:50:27.763848+00:00
-- url     : https://prove2.me/submissions/b3a395d6-1b7e-4bb5-a670-0e323541418e

/- InternLM Lean-Workbook, lean_workbook_12323, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution : ∀ {α β : ℚ}, α < β → α < (α + β) / 2 ∧ (α + β) / 2 < β  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | rintro α β h
      constructor <;> linarith
  | solve
    | intro α β hαβ
      constructor <;> linarith
  | solve
    | intro α β h
      constructor
      linarith
      linarith
  | solve
    | intros α β h
      refine' ⟨_, _⟩
      linarith
      linarith
  | solve
    | rintro α β h
      constructor <;> nlinarith
  | solve
    | intro α β hαβ
      constructor <;> nlinarith
  | solve
    | intro α β h
      constructor
      nlinarith
      nlinarith
  | solve
    | intros α β h
      refine' ⟨_, _⟩
      nlinarith
      nlinarith
example : (∀ {α β : ℚ}, α < β → α < (α + β) / 2 ∧ (α + β) / 2 < β) := @solution
#print axioms solution

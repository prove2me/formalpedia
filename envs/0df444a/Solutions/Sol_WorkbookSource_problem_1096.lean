-- Prove2me | solution 1 for WorkbookSource.problem_1096
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:40:57.79701+00:00
-- url     : https://prove2.me/submissions/b60c7655-4ccf-4039-a9d6-f9593f4c1548

/- InternLM Lean-Workbook, lean_workbook_1096, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution  (a b c : ℝ) :
  a * b + b * c + c * a - a * b * c ≤ (c^2 + 1) / 2 + (a^2 + b^2) / 2 ↔
  a^2 + b^2 + c^2 + 2 * a * b * c + 1 ≥ 2 * (a * b + b * c + c * a)  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | constructor <;> intro h <;> linarith
  | solve
    | constructor <;> intro h <;> linarith [h]
  | solve
    | constructor <;> intro h
      linarith
      linarith
  | solve
    | refine ⟨fun h ↦?_, fun h ↦?_⟩
      linarith
      linarith
  | solve
    | constructor <;> intro h <;> nlinarith
  | solve
    | constructor <;> intro h <;> nlinarith [h]
  | solve
    | constructor <;> intro h
      nlinarith
      nlinarith
  | solve
    | refine ⟨fun h ↦?_, fun h ↦?_⟩
      nlinarith
      nlinarith
example : (∀ (a b c : ℝ), a * b + b * c + c * a - a * b * c ≤ (c^2 + 1) / 2 + (a^2 + b^2) / 2 ↔
  a^2 + b^2 + c^2 + 2 * a * b * c + 1 ≥ 2 * (a * b + b * c + c * a)) := @solution
#print axioms solution

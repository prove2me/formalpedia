-- Prove2me | solution 1 for WorkbookSource.problem_48161
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:12:42.095207+00:00
-- url     : https://prove2.me/submissions/b57c74d0-4643-41d2-a21c-87f5aac23511

/- InternLM Lean-Workbook, lean_workbook_48161, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (x y z t : ℝ) : x - y + z - t = 1 ∧ 8 * x - 4 * y + 2 * z - t = 16 ∧ 27 * x - 9 * y + 3 * z - t = 81 ∧ 64 * x - 16 * y + 4 * z - t = 256 ↔ x = 10 ∧ y = 35 ∧ z = 50 ∧ t = 24  := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

example : (∀ (x y z t : ℝ), x - y + z - t = 1 ∧ 8 * x - 4 * y + 2 * z - t = 16 ∧ 27 * x - 9 * y + 3 * z - t = 81 ∧ 64 * x - 16 * y + 4 * z - t = 256 ↔ x = 10 ∧ y = 35 ∧ z = 50 ∧ t = 24) := @solution
#print axioms solution

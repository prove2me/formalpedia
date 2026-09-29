-- Prove2me | solution 1 for WorkbookSource.problem_24117
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:53:33.334671+00:00
-- url     : https://prove2.me/submissions/e5704ba8-293c-4657-820a-5c2c6ab4d341

/- InternLM Lean-Workbook, lean_workbook_24117, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (x : ℝ) : 3 - x > x + 1 ↔ x < 1  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | constructor
      all_goals intro h; linarith
  | solve
    | exact ⟨λ h ↦ by linarith, λ h ↦ by linarith⟩
  | solve
    | ring_nf
      constructor <;> intro h <;> linarith
  | solve
    | constructor
      intro h
      linarith
      intro h
      linarith
  | solve
    | constructor
      all_goals intro h; nlinarith
  | solve
    | exact ⟨λ h ↦ by nlinarith, λ h ↦ by nlinarith⟩
  | solve
    | ring_nf
      constructor <;> intro h <;> nlinarith
  | solve
    | constructor
      intro h
      nlinarith
      intro h
      nlinarith
example : (∀ (x : ℝ), 3 - x > x + 1 ↔ x < 1) := @solution
#print axioms solution

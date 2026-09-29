-- Prove2me | solution 1 for WorkbookSource.problem_16351
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:39:39.704986+00:00
-- url     : https://prove2.me/submissions/e3e3aaf9-0293-4a2d-8e17-316dd674189e

/- InternLM Lean-Workbook, lean_workbook_16351, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (a b : ℝ) : a + b = 6 ∧ a - b = 4 ↔ a = 5 ∧ b = 1  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | refine' ⟨fun h ↦ ⟨_, _⟩, fun h ↦ ⟨_, _⟩⟩ <;> linarith [h.1, h.2]
  | solve
    | refine' ⟨fun h ↦ ⟨_, _⟩, fun h ↦ ⟨_, _⟩⟩
      all_goals linarith [h.1, h.2]
  | solve
    | refine ⟨fun h ↦ ⟨?_,?_⟩, fun h ↦ ⟨?_,?_⟩⟩
      all_goals linarith [h.1, h.2]
  | solve
    | constructor
      rintro ⟨h₁, h₂⟩
      refine' ⟨_, _⟩
      linarith
      linarith
      rintro ⟨rfl, rfl⟩
      norm_num
  | solve
    | refine' ⟨fun h ↦ ⟨_, _⟩, fun h ↦ ⟨_, _⟩⟩ <;> nlinarith [h.1, h.2]
  | solve
    | refine' ⟨fun h ↦ ⟨_, _⟩, fun h ↦ ⟨_, _⟩⟩
      all_goals nlinarith [h.1, h.2]
  | solve
    | refine ⟨fun h ↦ ⟨?_,?_⟩, fun h ↦ ⟨?_,?_⟩⟩
      all_goals nlinarith [h.1, h.2]
  | solve
    | constructor
      rintro ⟨h₁, h₂⟩
      refine' ⟨_, _⟩
      nlinarith
      nlinarith
      rintro ⟨rfl, rfl⟩
      norm_num
example : (∀ (a b : ℝ), a + b = 6 ∧ a - b = 4 ↔ a = 5 ∧ b = 1) := @solution
#print axioms solution

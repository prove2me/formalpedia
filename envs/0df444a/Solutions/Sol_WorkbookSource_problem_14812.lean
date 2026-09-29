-- Prove2me | solution 1 for WorkbookSource.problem_14812
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:39:33.185983+00:00
-- url     : https://prove2.me/submissions/a1d3eccb-d909-4027-acb8-d8ea9564fb95

/- InternLM Lean-Workbook, lean_workbook_14812, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (f : ℝ → ℝ) (h₁ : Monotone f) (h₂ : ∀ x, f (f x) = (f x)^2) (h₃ : ∀ x, f (-f x) = (f x)^2) : ∀ x ∈ Set.range f, f x = f (-x)  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | rintro x ⟨x, rfl⟩
      simp [h₂, h₃]
  | solve
    | intro x ⟨y, hy⟩
      rw [←hy]
      simp [h₂, h₃, h₁]
  | solve
    | intro x hx
      obtain ⟨y, rfl⟩ := hx
      simp [h₂, h₃]
  | solve
    | intro x hx
      obtain ⟨y, rfl⟩ := hx
      simp only [h₂, h₃]
example : (∀ (f : ℝ → ℝ) (h₁ : Monotone f) (h₂ : ∀ x, f (f x) = (f x)^2) (h₃ : ∀ x, f (-f x) = (f x)^2), ∀ x ∈ Set.range f, f x = f (-x)) := @solution
#print axioms solution

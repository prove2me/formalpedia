-- Prove2me | solution 1 for WorkbookSource.problem_45429
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:17:54.266166+00:00
-- url     : https://prove2.me/submissions/1cd8b0ea-af63-4d06-9c6e-588f97681ccc

/- InternLM Lean-Workbook, lean_workbook_45429, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (a : ℝ) (h : a = -2) : 
  IsGreatest ({-3*a, 4*a, 24/a, a^2, 1} : Set ℝ) 6  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | rw [h]
      norm_num [IsGreatest]
  | solve
    | rw [h]
      refine' ⟨by norm_num, fun x hx => _⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with (rfl | rfl | rfl | rfl | rfl) <;> norm_num
  | solve
    | subst h
      refine' ⟨by norm_num, fun x hx => _⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with (rfl | rfl | rfl | rfl | rfl)
      all_goals norm_num [sq_nonneg]
  | solve
    | rw [h]
      simp only [IsGreatest]
      refine' ⟨by norm_num, fun x hx => _⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with (rfl | rfl | rfl | rfl | rfl)
      all_goals norm_num
example : (∀ (a : ℝ) (h : a = -2), IsGreatest ({-3*a, 4*a, 24/a, a^2, 1} : Set ℝ) 6) := @solution
#print axioms solution

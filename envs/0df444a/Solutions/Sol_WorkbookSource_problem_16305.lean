-- Prove2me | solution 1 for WorkbookSource.problem_16305
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:39:38.891405+00:00
-- url     : https://prove2.me/submissions/95b2de3d-91ad-4907-b5be-dcdbb67c453c

/- InternLM Lean-Workbook, lean_workbook_16305, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (a b c : ℝ) (h₁ : a = 2021) (h₂ : b = 2022) (h₃ : c = 2023) : (a + b + c)/6 = 1011  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | subst a b c
      ring
  | solve
    | subst a b c
      norm_num
  | solve
    | simp [h₁, h₂, h₃]
      ring
  | solve
    | rw [h₁, h₂, h₃]
      ring_nf
example : (∀ (a b c : ℝ) (h₁ : a = 2021) (h₂ : b = 2022) (h₃ : c = 2023), (a + b + c)/6 = 1011) := @solution
#print axioms solution

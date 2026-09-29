-- Prove2me | solution 1 for WorkbookSource.problem_33186
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:07:08.965495+00:00
-- url     : https://prove2.me/submissions/579b7def-34b4-4098-98b3-dde3d6aa2b23

/- InternLM Lean-Workbook, lean_workbook_33186, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Complex
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (z : ℂ) (n : ℤ) : ‖z^n‖ = ‖z‖^n  := by
  first
  | solve
    | exact norm_zpow _ _
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | rw [norm_zpow]
  | solve
    | exact norm_zpow _ _
  | solve
    | simp [Complex.norm_eq_abs]
  | solve
    | simp [norm_eq_abs, abs_pow]
  | solve
    | rw [Complex.norm_eq_abs, Complex.norm_eq_abs, Complex.abs_zpow]
example : (∀ (z : ℂ) (n : ℤ), ‖z^n‖ = ‖z‖^n) := @solution
#print axioms solution

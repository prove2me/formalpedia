-- Prove2me | solution 1 for WorkbookSource.problem_24733
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:57:11.735168+00:00
-- url     : https://prove2.me/submissions/8aae37b9-41db-49da-b461-69e7c7baaea4

/- InternLM Lean-Workbook, lean_workbook_24733, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution  (s : ℝ)
  (h₀ : 0 < s)
  (h₁ : Real.sqrt (3 * s^2 + 25) = 10) :
  s = 5  := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 * s^2 + 25 by positivity)
  rw [h₁] at hs
  nlinarith [sq_nonneg (s - 5)]

example : (∀ (s : ℝ)
  (h₀ : 0 < s)
  (h₁ : Real.sqrt (3 * s^2 + 25) = 10), s = 5) := @solution
#print axioms solution

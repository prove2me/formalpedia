-- Prove2me | solution 1 for WorkbookSource.problem_32497
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:05:54.321108+00:00
-- url     : https://prove2.me/submissions/76a614b6-dc1a-4c6f-a52f-2f47805934f3

/- InternLM Lean-Workbook, lean_workbook_32497, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxRecDepth 10000
set_option exponentiation.threshold 4096
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution  (a b : ℝ)
  (h₀ : 0 ≤ a ∧ a ≤ b) :
  a / (1 + a) ≤ b / (1 + b)  := by
  apply (div_le_div_iff₀ (by nlinarith [h₀.1]) (by nlinarith [h₀.1,h₀.2])).2
  nlinarith [h₀.2]

example : (∀ (a b : ℝ)
  (h₀ : 0 ≤ a ∧ a ≤ b), a / (1 + a) ≤ b / (1 + b)) := @solution
#print axioms solution

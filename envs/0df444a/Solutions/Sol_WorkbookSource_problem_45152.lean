-- Prove2me | solution 1 for WorkbookSource.problem_45152
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:52:10.943314+00:00
-- url     : https://prove2.me/submissions/5ca3d3c4-96d8-46cc-97fe-e936975f4998

/- InternLM Lean-Workbook, lean_workbook_45152, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution  (x y z : ℝ)
  (a : ℝ)
  (h₀ : x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0)
  (h₁ : a = x * y * z - 1 / (x * y * z))
  (h₂ : x - 1/y = a/6)
  (h₃ : y - 1/z = a/3)
  (h₄ : z - 1/x = a/2) :
  x + y + z - 1/x - 1/y - 1/z = a  := by
  first
  | solve
    | linarith [h₂,h₃,h₄]
  | solve
    | field_simp [h₁, h₂, h₃, h₄]
      linarith
  | solve
    | linarith [h₁, h₂, h₃, h₄]
  | solve
    | simp [h₁, h₂, h₃, h₄] at *
      linarith [h₀.1, h₀.2.1, h₀.2.2]
example : (∀ (x y z : ℝ)
  (a : ℝ)
  (h₀ : x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0)
  (h₁ : a = x * y * z - 1 / (x * y * z))
  (h₂ : x - 1/y = a/6)
  (h₃ : y - 1/z = a/3)
  (h₄ : z - 1/x = a/2), x + y + z - 1/x - 1/y - 1/z = a) := @solution
#print axioms solution

-- Prove2me | solution 1 for WorkbookSource.problem_41120
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:43:53.950959+00:00
-- url     : https://prove2.me/submissions/200deeba-bd23-45d2-b637-5c58d4b6ed90

/- InternLM Lean-Workbook, lean_workbook_41120, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) (h₁ : a = 14) (h₂ : b = 1) (h₃ : c = 15) : a^2 + b^2 + c^2 = 422  := by
  first
  | solve
    | norm_num [h₁,h₂,h₃]
  | solve
    | simp [h₁, h₂, h₃, sq, add_assoc, add_comm, add_left_comm]
      norm_num
  | solve
    | subst h₁ h₂ h₃
      ring
  | solve
    | simp only [h₁, h₂, h₃, pow_two]
      ring
  | solve
    | simp only [h₁, h₂, h₃, pow_two]
      norm_num [h₁, h₂, h₃]
  | solve
    | simp only [h₁, h₂, h₃, sq]
      norm_num [h₁, h₂, h₃]
  | solve
    | rw [h₁, h₂, h₃]
      norm_num
  | solve
    | simp [h₁, h₂, h₃, sq]
      norm_cast
  | solve
    | rw [h₁, h₂, h₃]
      ring
  | solve
    | rw [h₁, h₂, h₃, show (14 : ℝ)^2 + 1^2 + 15^2 = 422 by norm_num]
  | solve
    | field_simp [h₁, h₂, h₃]
      ring
  | solve
    | rw [h₁, h₂, h₃]
      linear_combination 14^2 + 1^2 + 15^2 - 422
  | solve
    | rw [h₁, h₂, h₃]
      linarith
  | solve
    | rw [h₁, h₂, h₃]
      norm_num at h₁ h₂ h₃ ⊢
  | solve
    | simp only [h₁, h₂, h₃]
      norm_num [h₁, h₂, h₃]
  | solve
    | rw [h₁, h₂, h₃]
      ring_nf at h₁ h₂ h₃ ⊢
  | solve
    | simp [h₁, h₂, h₃, sq]
      norm_num
  | solve
    | subst h₁ h₂ h₃
      norm_num
  | solve
    | simp [h₁, h₂, h₃]
      norm_num [h₁, h₂, h₃]
  | solve
    | simp only [h₁, h₂, h₃, sq, add_assoc, add_comm, add_left_comm]
      norm_num
  | solve
    | simp only [h₁, h₂, h₃, sq]
      norm_num at *
  | solve
    | simp [h₁, h₂, h₃, _root_.pow_two]
      norm_num [h₁, h₂, h₃]
  | solve
    | substs a b c
      ring
  | solve
    | rw [h₁, h₂, h₃]
      norm_num at *
  | solve
    | simp [h₁, h₂, h₃, add_comm]
      ring
  | solve
    | ring_nf
      simp only [h₁, h₂, h₃]
      norm_num [h₁, h₂, h₃]
  | solve
    | simp [h₂, h₃, h₁]
      ring_nf
  | solve
    | rw [h₁, h₂, h₃] at *
      linarith
example : (∀ (a b c : ℝ) (h₁ : a = 14) (h₂ : b = 1) (h₃ : c = 15), a^2 + b^2 + c^2 = 422) := @solution
#print axioms solution

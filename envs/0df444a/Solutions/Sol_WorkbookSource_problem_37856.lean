-- Prove2me | solution 1 for WorkbookSource.problem_37856
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:43:42.10828+00:00
-- url     : https://prove2.me/submissions/305357c2-56c1-49a9-b4f2-322ab111e754

/- InternLM Lean-Workbook, lean_workbook_37856, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (x y z : ℝ) (h₁ : x * y * z = 33) (h₂ : y = 1) (h₃ : z = 3) : x = 11  := by
  first
  | solve
    | rw [h₂,h₃] at h₁
      linarith
  | solve
    | simp [h₂, h₃] at h₁
      rw [eq_comm] at h₁
      linarith
  | solve
    | rw [h₂, h₃] at h₁
      field_simp at h₁
      linarith [h₁]
  | solve
    | subst h₂
      subst h₃
      nlinarith [h₁]
  | solve
    | simp only [h₂, h₃] at h₁
      field_simp at h₁ ⊢
      linarith
  | solve
    | simp [h₂, h₃] at h₁
      nlinarith
  | solve
    | rw [h₂, h₃] at h₁
      rw [← mul_left_inj' (by norm_num : (3 : ℝ) ≠ 0)] at h₁
      linarith [h₁]
  | solve
    | rw [h₂, h₃] at h₁
      rw [mul_one, mul_comm] at h₁
      linarith [h₁, h₂, h₃]
  | solve
    | simp only [h₂, h₃] at h₁
      linarith only [h₁]
  | solve
    | rw [h₃] at h₁
      rw [h₂] at h₁
      linarith
  | solve
    | simp [h₂, h₃] at h₁
      linarith
  | solve
    | rw [h₂, h₃] at h₁
      linarith [h₁, h₂, h₃]
  | solve
    | simp only [h₂, h₃] at h₁
      linarith
  | solve
    | rw [h₂, h₃] at h₁
      rw [mul_assoc] at h₁
      linarith
  | solve
    | simp [h₂, h₃] at h₁
      linarith [h₁]
  | solve
    | simp [h₂, h₃] at h₁ ⊢
      linarith
  | solve
    | rw [h₂, h₃] at h₁
      field_simp at h₁
      linarith
  | solve
    | subst h₂ h₃
      nlinarith
  | solve
    | rw [h₂] at h₁
      rw [h₃] at h₁
      linarith
  | solve
    | simp [h₃, h₂] at h₁
      linarith [h₁, h₂, h₃]
  | solve
    | rw [h₂, h₃] at h₁
      field_simp [h₁, h₂, h₃] at h₁ ⊢
      linarith only [h₁]
  | solve
    | subst h₂
      subst h₃
      field_simp at h₁
      linarith
  | solve
    | subst h₂ h₃
      field_simp at h₁ ⊢
      linarith
  | solve
    | simp [h₂, h₃] at h₁ ⊢
      linarith [h₁]
  | solve
    | simp only [h₂, h₃] at h₁
      rw [mul_assoc] at h₁
      linarith
  | solve
    | subst h₂ h₃
      linarith
  | solve
    | simp [h₂, h₃] at h₁
      linarith only [h₁, h₂, h₃]
  | solve
    | subst y z
      linarith
  | solve
    | simp [h₁, h₂, h₃] at *
      linarith
  | solve
    | simp [h₁, h₂, h₃] at *
      nlinarith
  | solve
    | subst h₂
      subst h₃
      linarith only [h₁]
example : (∀ (x y z : ℝ) (h₁ : x * y * z = 33) (h₂ : y = 1) (h₃ : z = 3), x = 11) := @solution
#print axioms solution

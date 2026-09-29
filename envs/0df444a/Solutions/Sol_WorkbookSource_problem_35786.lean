-- Prove2me | solution 1 for WorkbookSource.problem_35786
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:39:56.267354+00:00
-- url     : https://prove2.me/submissions/4eaf7245-c558-4843-a1af-f580b0e71a58

/- InternLM Lean-Workbook, lean_workbook_35786, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution  (c : ℝ)
  (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = x^2 - 5 * x + 3 * c)
  (h₁ : f 3 = -12) :
  c = -2  := by
  first
  | solve
    | have := h₀ 3
      norm_num at this
      linarith
  | solve
    | have h₃ : f 3 = 3^2 - 5 * 3 + 3 * c := h₀ 3
      linarith
  | solve
    | simp [h₀, h₁] at *
      linarith [h₀, h₁]
  | solve
    | simp_all
      linarith [h₀, h₁]
  | solve
    | simp [h₀] at h₁
      linarith [h₀, h₁]
  | solve
    | simp [h₀, h₁] at *
      linarith only [h₀, h₁]
  | solve
    | norm_num
      have h₂ := h₀ 3
      linarith [h₁, h₂]
  | solve
    | rw [h₀] at h₁
      norm_num at h₁
      linarith [h₁, h₀]
  | solve
    | simp [h₀] at h₁
      linarith [h₀]
  | solve
    | field_simp [h₀] at h₁
      linarith [h₀ 3, h₁]
  | solve
    | rw [h₀] at h₁
      norm_num at h₁
      linarith
  | solve
    | simp only [h₀, h₁] at *
      linarith [h₁]
  | solve
    | simp [h₀, h₁] at *
      linarith
  | solve
    | rw [h₀] at h₁
      linarith
  | solve
    | have h₂ := h₀ 3
      norm_num at *
      linarith [h₀ 3, h₁]
  | solve
    | simp [h₀, h₁] at h₁
      linarith [h₀ 3, h₁]
  | solve
    | rw [h₀] at h₁
      norm_num at h₁
      linarith [h₀ 3, h₁]
  | solve
    | rw [h₀] at h₁
      linarith only [h₀, h₁]
  | solve
    | simp only [h₀] at h₁
      linarith [h₁]
  | solve
    | have h₂ : f 3 = 3^2 - (5 * 3) + 3 * c := h₀ 3
      linarith [h₁, h₂]
  | solve
    | simp [h₀] at h₁
      linarith [h₀ 0, h₀ 1, h₀ (-1)]
  | solve
    | simp [h₀] at h₁
      linarith only [h₁]
  | solve
    | simp [h₀, h₁] at h₁ ⊢
      linarith only [h₀, h₁]
  | solve
    | norm_num at *
      specialize h₀ 3
      linarith [h₀, h₁]
  | solve
    | specialize h₀ 3
      rw [h₁] at h₀
      linarith [h₁, h₀]
  | solve
    | rw [h₀] at h₁
      linarith [h₀, h₁]
  | solve
    | have h₂ := h₀ 3
      simp [h₁, h₂] at *
      linarith
  | solve
    | have h₂ : f 3 = 3^2 - 5 * 3 + 3 * c := h₀ 3
      linarith
  | solve
    | simp only [h₀, h₁] at *
      linarith [h₀, h₁]
  | solve
    | field_simp [h₀] at h₁
      linarith
  | solve
    | rw [h₀] at h₁
      norm_num at h₁
      linarith [h₀, h₁]
example : (∀ (c : ℝ)
  (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = x^2 - 5 * x + 3 * c)
  (h₁ : f 3 = -12), c = -2) := @solution
#print axioms solution

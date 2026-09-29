-- Prove2me | solution 1 for WorkbookSource.problem_43229
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:43:56.107599+00:00
-- url     : https://prove2.me/submissions/461e3e95-3771-480a-a05e-70561e90d75a

/- InternLM Lean-Workbook, lean_workbook_43229, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution  (a b c : ℝ) :
  a * b * (a + b) + b * c * (b + c) + c * a * (c + a) ≥
  (3 * (a + b) * (b + c) * (c + a)) / 4 ↔
  a * b * (a + b) + b * c * (b + c) + c * a * (c + a) ≥
  6 * a * b * c  := by
  first
  | solve
    | constructor <;> intro h <;> nlinarith
  | solve
    | field_simp [mul_assoc]
      constructor <;> intro h
      linarith
      nlinarith
  | solve
    | constructor
      intro h
      linarith
      intro h
      linarith
  | solve
    | refine' ⟨fun h => _, fun h => _⟩
      linarith
      field_simp at h
      linarith
  | solve
    | field_simp [mul_add, add_mul]
      ring_nf
      constructor <;> intro h
      linarith
      linarith [h]
  | solve
    | constructor <;> intro h
      field_simp [mul_comm] at h
      linarith
      nlinarith
  | solve
    | constructor <;> intro h <;> linarith
  | solve
    | constructor
      intro h
      linarith [h]
      intro h
      nlinarith
  | solve
    | constructor
      intro h
      field_simp at h
      linarith
      intro h
      nlinarith
  | solve
    | constructor <;> intro h
      linarith [h]
      linarith
  | solve
    | refine' ⟨fun h => _, fun h => _⟩
      field_simp at h ⊢
      nlinarith
      field_simp at h ⊢
      ring_nf at h ⊢
      nlinarith
  | solve
    | simp only [ge_iff_le]
      field_simp [mul_add, add_mul]
      ring_nf
      constructor <;> intro h <;> linarith
example : (∀ (a b c : ℝ), a * b * (a + b) + b * c * (b + c) + c * a * (c + a) ≥
  (3 * (a + b) * (b + c) * (c + a)) / 4 ↔
  a * b * (a + b) + b * c * (b + c) + c * a * (c + a) ≥
  6 * a * b * c) := @solution
#print axioms solution

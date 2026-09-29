-- Prove2me | solution 1 for WorkbookSource.problem_35932
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:39:57.210732+00:00
-- url     : https://prove2.me/submissions/1f0a6eac-ee10-4192-8bb4-a981e872d65c

/- InternLM Lean-Workbook, lean_workbook_35932, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (x : ℝ) : x + 2 < 1 ↔ x < -1  := by
  first
  | solve
    | constructor <;> intro h <;> linarith
  | solve
    | rw [← neg_lt_neg_iff]
      simp [sub_eq_add_neg]
      constructor <;> intro h <;> linarith [h]
  | solve
    | exact ⟨fun h ↦ by linarith, fun h ↦ by linarith⟩
  | solve
    | apply Iff.intro
      intro hx
      linarith only [hx]
      intro hx
      linarith only [hx]
  | solve
    | rw [lt_iff_not_le, lt_iff_not_le]
      norm_num
      constructor <;> intro h <;> linarith
  | solve
    | exact ⟨fun h ↦ by linarith [h], fun h ↦ by linarith⟩
  | solve
    | refine' ⟨fun h => by linarith, fun h => by linarith⟩
  | solve
    | constructor
      intro hx
      linarith
      intro hx
      linarith [hx]
  | solve
    | refine' ⟨fun h => _, fun h => _⟩
      linarith only [h]
      linarith only [h]
  | solve
    | constructor
      intro h
      linarith only [h]
      rintro h
      linarith only [h]
  | solve
    | exact ⟨fun h ↦ by linarith [h], fun h ↦ by linarith [h]⟩
  | solve
    | rw [lt_iff_not_le]
      rw [← not_le]
      norm_num
      constructor <;> intro h <;> linarith
  | solve
    | constructor
      intro hx
      linarith
      intro hx
      linarith only [hx]
  | solve
    | rw [← neg_lt_neg_iff]
      simp only [neg_add, neg_lt_neg_iff]
      constructor <;> intro h
      linarith [h]
      linarith [h]
  | solve
    | constructor
      intro hx
      linarith
      intro hx
      linarith
  | solve
    | exact
      ⟨fun h => by linarith [h], fun h => by linarith [h]⟩
  | solve
    | constructor <;> intro h
      linarith only [h]
      linarith only [h]
  | solve
    | constructor
      intro h
      linarith [h]
      rintro h
      linarith
  | solve
    | exact ⟨fun h => by linarith, fun h => by linarith⟩
  | solve
    | constructor
      intro h
      linarith
      intro h
      linarith
  | solve
    | rw [← neg_lt_neg_iff]
      simp [sub_eq_add_neg]
      constructor <;> intro h <;> linarith
  | solve
    | refine' ⟨fun h => by linarith [h], fun h => by linarith⟩
  | solve
    | exact ⟨fun hx => by linarith [hx], fun hx => by linarith [hx]⟩
  | solve
    | exact ⟨fun h => by linarith [h], fun h => by linarith⟩
  | solve
    | rw [← neg_lt_neg_iff]
      simp [sub_eq_add_neg]
      constructor <;> intro h
      linarith [h]
      linarith
  | solve
    | constructor
      intro h
      contrapose! h
      linarith
      intro h
      linarith
example : (∀ (x : ℝ), x + 2 < 1 ↔ x < -1) := @solution
#print axioms solution

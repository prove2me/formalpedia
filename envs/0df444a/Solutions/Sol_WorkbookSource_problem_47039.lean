-- Prove2me | solution 1 for WorkbookSource.problem_47039
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:52:15.772048+00:00
-- url     : https://prove2.me/submissions/a807643a-2473-4ddb-b052-65b738156fd7

/- InternLM Lean-Workbook, lean_workbook_47039, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (x y : ℝ) (h : x > y) (h' : y > -1) : (x / (1 + x)) > (y / (1 + y))  := by
  first
  | solve
    | have hy : 0 < 1+y := by linarith
      have hx : 0 < 1+x := by linarith
      apply (div_lt_div_iff₀ hy hx).2
      nlinarith
  | solve
    | field_simp [add_comm]
      rw [div_lt_div_iff]
      nlinarith
      linarith
      linarith [h']
  | solve
    | field_simp [add_comm]
      refine' (div_lt_div_iff (by linarith) (by linarith)).mpr _
      nlinarith
  | solve
    | field_simp [add_comm]
      rw [div_lt_div_iff]
      nlinarith
      nlinarith [h, h']
      nlinarith [h, h']
  | solve
    | field_simp [add_comm]
      rw [div_lt_div_iff]
      nlinarith
      linarith [h, h']
      nlinarith [h, h']
  | solve
    | field_simp [add_comm]
      rw [div_lt_div_iff]
      nlinarith
      linarith
      linarith
  | solve
    | field_simp [add_comm] at *
      rw [div_lt_div_iff]
      nlinarith
      nlinarith
      nlinarith
  | solve
    | field_simp [add_comm]
      rw [div_lt_div_iff]
      nlinarith
      linarith [h']
      nlinarith
  | solve
    | field_simp [add_comm]
      rw [div_lt_div_iff]
      nlinarith
      linarith [h, h']
      linarith [h, h']
example : (∀ (x y : ℝ) (h : x > y) (h' : y > -1), (x / (1 + x)) > (y / (1 + y))) := @solution
#print axioms solution

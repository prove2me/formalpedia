-- Prove2me | solution 1 for WorkbookTyped.plus_44637
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:44:33.774424+00:00
-- url     : https://prove2.me/submissions/30c26b67-1362-48ca-b157-e19244a0c45a

/- Source: InternLM Lean-Workbook, lean_workbook_plus_44637. Apache-2.0.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json
This is an explicit-binder repair, not an unchanged formal declaration.
Added explicit real binders (a b c : ℝ) and real base annotations so every variable exponent uses Real.rpow. The old simp proof depended on natural-number inference and does not prove this repaired theorem. A new argument proves the intended real-exponent inequality. -/
import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000

private lemma eight_rpow (t : ℝ) : (8 : ℝ)^t = ((2 : ℝ)^t)^3 := by
  calc
    (8 : ℝ)^t = ((2 : ℝ)^ (3 : ℕ))^t := by norm_num
    _ = (2 : ℝ)^((3 : ℝ)*t) := (Real.rpow_natCast_mul (by norm_num) 3 t).symm
    _ = ((2 : ℝ)^t)^3 := by
      rw [mul_comm]
      exact Real.rpow_mul_natCast (by norm_num) t 3

theorem solution (a b c : ℝ) : a + b + c = 0 → (8 : ℝ)^a + (8 : ℝ)^b + (8 : ℝ)^c ≥ (2 : ℝ)^a + (2 : ℝ)^b + (2 : ℝ)^c := by
  intro habc
  have hsum : 3 ≤ (2 : ℝ)^a + (2 : ℝ)^b + (2 : ℝ)^c := by
    have ha := Real.add_one_le_exp (Real.log 2 * a)
    have hb := Real.add_one_le_exp (Real.log 2 * b)
    have hc := Real.add_one_le_exp (Real.log 2 * c)
    rw [← Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)] at ha hb hc
    have hz : Real.log 2 * a + Real.log 2 * b + Real.log 2 * c = 0 := by rw [← mul_add, ← mul_add, habc, mul_zero]
    linarith
  have hcube : ∀ x : ℝ, 0 ≤ x → 3*x-2 ≤ x^3 := by
    intro x hx
    nlinarith [mul_nonneg (sq_nonneg (x-1)) (show 0 ≤ x+2 by linarith)]
  rw [eight_rpow, eight_rpow, eight_rpow]
  have ha := hcube ((2 : ℝ)^a) (Real.rpow_nonneg (by norm_num) _)
  have hb := hcube ((2 : ℝ)^b) (Real.rpow_nonneg (by norm_num) _)
  have hc := hcube ((2 : ℝ)^c) (Real.rpow_nonneg (by norm_num) _)
  linarith

example : (∀ (a b c : ℝ), a + b + c = 0 → (8 : ℝ)^a + (8 : ℝ)^b + (8 : ℝ)^c ≥ (2 : ℝ)^a + (2 : ℝ)^b + (2 : ℝ)^c) := @solution
#print axioms solution

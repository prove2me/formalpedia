-- Prove2me | solution 1 for congruent_number_problem
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:03:52.161354+00:00
-- url     : https://prove2.me/submissions/f91d1df6-c5a6-4f2e-bbaf-36c7526f4663

import Mathlib

set_option autoImplicit false

private theorem triangle_to_point
    (n a b c : ℚ) (ha : 0 < a) (hb : 0 < b)
    (htri : a ^ 2 + b ^ 2 = c ^ 2) (harea : a * b / 2 = n) :
    ∃ x y : ℚ, y ^ 2 = x ^ 3 - n ^ 2 * x ∧ y ≠ 0 := by
  have hca : a + c ≠ 0 := by
    intro h
    have hc : c = -a := by linarith
    rw [hc] at htri
    nlinarith [sq_pos_of_pos hb]
  refine ⟨a * (a + c) / 2, a ^ 2 * (a + c) / 2, ?_, ?_⟩
  · rw [← harea]
    linear_combination (a ^ 3 * (a + c) / 8) * htri
  · exact div_ne_zero (mul_ne_zero (pow_ne_zero 2 (ne_of_gt ha)) hca)
      (by norm_num)

private theorem point_to_triangle
    (n x y : ℚ) (hn : 0 < n)
    (hcurve : y ^ 2 = x ^ 3 - n ^ 2 * x) (hy : y ≠ 0) :
    ∃ a b c : ℚ, 0 < a ∧ 0 < b ∧ 0 < c ∧
      a ^ 2 + b ^ 2 = c ^ 2 ∧ a * b / 2 = n := by
  have hy2 : y ^ 2 ≠ 0 := pow_ne_zero 2 hy
  have hx : x ≠ 0 := by
    intro h
    apply hy2
    simpa [h] using hcurve
  have hdiff : x ^ 2 - n ^ 2 ≠ 0 := by
    intro h
    apply hy2
    linear_combination hcurve + x * h
  have harea : ((x ^ 2 - n ^ 2) / y) * (2 * n * x / y) / 2 = n := by
    field_simp
    linear_combination -hcurve
  refine ⟨|(x ^ 2 - n ^ 2) / y|, |2 * n * x / y|,
    |(x ^ 2 + n ^ 2) / y|, ?_, ?_, ?_, ?_, ?_⟩
  · exact abs_pos.mpr (div_ne_zero hdiff hy)
  · exact abs_pos.mpr (div_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt hn)) hx) hy)
  · exact abs_pos.mpr (div_ne_zero
      (ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg x) (sq_pos_of_pos hn))) hy)
  · simp only [sq_abs]
    ring
  · calc
      |(x ^ 2 - n ^ 2) / y| * |2 * n * x / y| / 2 =
          |((x ^ 2 - n ^ 2) / y) * (2 * n * x / y) / 2| := by
            simp only [abs_div, abs_mul]
            norm_num
      _ = n := by rw [harea, abs_of_pos hn]

theorem solution (n : ℕ) (hn : 0 < n) (_hsqfree : Squarefree n) :
    (∃ a b c : ℚ, 0 < a ∧ 0 < b ∧ 0 < c ∧
      a ^ 2 + b ^ 2 = c ^ 2 ∧ a * b / 2 = n) ↔
    (∃ x y : ℚ, y ^ 2 = x ^ 3 - (n : ℚ) ^ 2 * x ∧ y ≠ 0) := by
  constructor
  · rintro ⟨a, b, c, ha, hb, _, htri, harea⟩
    exact triangle_to_point n a b c ha hb htri harea
  · rintro ⟨x, y, hcurve, hy⟩
    exact point_to_triangle n x y (by exact_mod_cast hn) hcurve hy

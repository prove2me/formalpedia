-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P42.gordonMetric_inverse
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T23:55:34.076993+00:00
-- url     : https://prove2.me/submissions/b855b76b-d549-4060-81c6-ebad1a3ab62d

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P42
open QAlgorithms.Papers.Independent.Renew46.P42

noncomputable section

open scoped BigOperators

open Filter Set MeasureTheory

-- Reuse the pinned accepted real quadratic form (arbitrary finite real matrices).

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

theorem g64h_prodDU (a b : ℝ) (U : V4)
    (hQ : U 0 * U 0 - U 1 * U 1 - U 2 * U 2 - U 3 * U 3 = 1) (hab : a + b + a * b = 0) :
    (Matrix.of fun i j : Fin 4 => minkowskiMetric i j + a * apply4 minkowskiMetric U i * apply4 minkowskiMetric U j) *
    (Matrix.of fun i j : Fin 4 => minkowskiMetric i j + b * U i * U j) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_four, apply4, minkowskiMetric, Matrix.one_apply]
  · linear_combination (a * b * U 0 * U 0) * hQ + (U 0 * U 0) * hab
  · linear_combination (a * b * U 0 * U 1) * hQ + (U 0 * U 1) * hab
  · linear_combination (a * b * U 0 * U 2) * hQ + (U 0 * U 2) * hab
  · linear_combination (a * b * U 0 * U 3) * hQ + (U 0 * U 3) * hab
  · linear_combination (a * b * (-U 1) * U 0) * hQ + ((-U 1) * U 0) * hab
  · linear_combination (a * b * (-U 1) * U 1) * hQ + ((-U 1) * U 1) * hab
  · linear_combination (a * b * (-U 1) * U 2) * hQ + ((-U 1) * U 2) * hab
  · linear_combination (a * b * (-U 1) * U 3) * hQ + ((-U 1) * U 3) * hab
  · linear_combination (a * b * (-U 2) * U 0) * hQ + ((-U 2) * U 0) * hab
  · linear_combination (a * b * (-U 2) * U 1) * hQ + ((-U 2) * U 1) * hab
  · linear_combination (a * b * (-U 2) * U 2) * hQ + ((-U 2) * U 2) * hab
  · linear_combination (a * b * (-U 2) * U 3) * hQ + ((-U 2) * U 3) * hab
  · linear_combination (a * b * (-U 3) * U 0) * hQ + ((-U 3) * U 0) * hab
  · linear_combination (a * b * (-U 3) * U 1) * hQ + ((-U 3) * U 1) * hab
  · linear_combination (a * b * (-U 3) * U 2) * hQ + ((-U 3) * U 2) * hab
  · linear_combination (a * b * (-U 3) * U 3) * hQ + ((-U 3) * U 3) * hab

theorem g64h_prodUD (a b : ℝ) (U : V4)
    (hQ : U 0 * U 0 - U 1 * U 1 - U 2 * U 2 - U 3 * U 3 = 1) (hab : a + b + a * b = 0) :
    (Matrix.of fun i j : Fin 4 => minkowskiMetric i j + b * U i * U j) *
    (Matrix.of fun i j : Fin 4 => minkowskiMetric i j + a * apply4 minkowskiMetric U i * apply4 minkowskiMetric U j) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_four, apply4, minkowskiMetric, Matrix.one_apply]
  · linear_combination (a * b * U 0 * U 0) * hQ + (U 0 * U 0) * hab
  · linear_combination (a * b * U 0 * (-U 1)) * hQ + (U 0 * (-U 1)) * hab
  · linear_combination (a * b * U 0 * (-U 2)) * hQ + (U 0 * (-U 2)) * hab
  · linear_combination (a * b * U 0 * (-U 3)) * hQ + (U 0 * (-U 3)) * hab
  · linear_combination (a * b * U 1 * U 0) * hQ + (U 1 * U 0) * hab
  · linear_combination (a * b * U 1 * (-U 1)) * hQ + (U 1 * (-U 1)) * hab
  · linear_combination (a * b * U 1 * (-U 2)) * hQ + (U 1 * (-U 2)) * hab
  · linear_combination (a * b * U 1 * (-U 3)) * hQ + (U 1 * (-U 3)) * hab
  · linear_combination (a * b * U 2 * U 0) * hQ + (U 2 * U 0) * hab
  · linear_combination (a * b * U 2 * (-U 1)) * hQ + (U 2 * (-U 1)) * hab
  · linear_combination (a * b * U 2 * (-U 2)) * hQ + (U 2 * (-U 2)) * hab
  · linear_combination (a * b * U 2 * (-U 3)) * hQ + (U 2 * (-U 3)) * hab
  · linear_combination (a * b * U 3 * U 0) * hQ + (U 3 * U 0) * hab
  · linear_combination (a * b * U 3 * (-U 1)) * hQ + (U 3 * (-U 1)) * hab
  · linear_combination (a * b * U 3 * (-U 2)) * hQ + (U 3 * (-U 2)) * hab
  · linear_combination (a * b * U 3 * (-U 3)) * hQ + (U 3 * (-U 3)) * hab

/-- PDF p.5, (42)–(43): both Gordon inverse identities, with eta-normalized flow. -/
theorem solution (c n : ℝ) (u : V3)
    (hc : 0 < c) (hn : 1 ≤ n) (hu : dot3 u u < c ^ 2) :
    quadratic minkowskiMetric (fourFlow c u) = 1 ∧
    gDown c n u * gUp c n u = 1 ∧ gUp c n u * gDown c n u = 1 := by
  have hc2 : 0 < c ^ 2 := by positivity
  have hpos : 0 < 1 - dot3 u u / c ^ 2 := by rw [sub_pos, div_lt_one hc2]; exact hu
  have hγ2 : lorentzFactor c u ^ 2 * (1 - dot3 u u / c ^ 2) = 1 := by
    have hcu : c ^ 2 - dot3 u u ≠ 0 := by linarith
    rw [lorentzFactor, div_pow, Real.sq_sqrt hpos.le]; field_simp
  have hs' : dot3 u u = u 0 * u 0 + u 1 * u 1 + u 2 * u 2 := by simp [dot3, Fin.sum_univ_three]
  have hQ : fourFlow c u 0 * fourFlow c u 0 - fourFlow c u 1 * fourFlow c u 1 -
      fourFlow c u 2 * fourFlow c u 2 - fourFlow c u 3 * fourFlow c u 3 = 1 := by
    simp only [fourFlow]
    simp
    rw [hs'] at hγ2
    rw [← hγ2]; field_simp; ring
  have hn0 : n ≠ 0 := by positivity
  have hab : (1 / n ^ 2 - 1) + (n ^ 2 - 1) + (1 / n ^ 2 - 1) * (n ^ 2 - 1) = 0 := by
    field_simp; ring
  refine ⟨?_, ?_, ?_⟩
  · simp only [quadratic, Fin.sum_univ_four, minkowskiMetric]
    simp
    linear_combination hQ
  · exact g64h_prodDU _ _ _ hQ hab
  · exact g64h_prodUD _ _ _ hQ hab


end


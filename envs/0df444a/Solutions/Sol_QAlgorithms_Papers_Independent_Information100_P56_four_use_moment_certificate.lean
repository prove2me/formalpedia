-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P56.four_use_moment_certificate
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T03:44:48.922047+00:00
-- url     : https://prove2.me/submissions/3a0fdaa7-9b1c-4992-bb32-54ca3382c62b

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56

noncomputable section
open scoped ComplexConjugate ComplexOrder Matrix
open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P56

attribute [local instance] Classical.propDecidable

lemma g53i_w0 : fourWeight 0 = 23089 / 100000 := rfl
lemma g53i_w1 : fourWeight 1 = 33839 / 100000 := rfl
lemma g53i_w2 : fourWeight 2 = 27248 / 100000 := rfl
lemma g53i_w3 : fourWeight 3 = 11757 / 100000 := rfl
lemma g53i_w4 : fourWeight 4 = 4067 / 100000 := rfl

lemma g53i_fm0 : factorialMoment 0 = 1 := by
  norm_num [factorialMoment, g53i_w0, g53i_w1, g53i_w2, g53i_w3, g53i_w4, Fin.sum_univ_five, Nat.choose]
lemma g53i_fm1 : factorialMoment 1 = 69937 / 200000 := by
  norm_num [factorialMoment, g53i_w0, g53i_w1, g53i_w2, g53i_w3, g53i_w4, Fin.sum_univ_five, Nat.choose]
lemma g53i_fm2 : factorialMoment 2 = 86921 / 600000 := by
  norm_num [factorialMoment, g53i_w0, g53i_w1, g53i_w2, g53i_w3, g53i_w4, Fin.sum_univ_five, Nat.choose]
lemma g53i_fm3 : factorialMoment 3 = 1121 / 16000 := by
  norm_num [factorialMoment, g53i_w0, g53i_w1, g53i_w2, g53i_w3, g53i_w4, Fin.sum_univ_five, Nat.choose]
lemma g53i_fm4 : factorialMoment 4 = 4067 / 100000 := by
  norm_num [factorialMoment, g53i_w0, g53i_w1, g53i_w2, g53i_w3, g53i_w4, Fin.sum_univ_five, Nat.choose]

lemma g53i_det_eq (f : ℕ → ℝ) : Matrix.det (fun i j : Fin 3 => f (i.val + j.val)) =
    f 0 * (f 2 * f 4 - f 3 * f 3) - f 1 * (f 1 * f 4 - f 3 * f 2) + f 2 * (f 1 * f 3 - f 2 * f 2) := by
  have := Matrix.det_fin_three (Matrix.of fun i j : Fin 3 => f (i.val + j.val))
  simp only [Matrix.of_apply] at this
  erw [this]; simp; ring

/-- Section VII D, p.20, Eq.(75): exact rational moment certificate and the
nonrepresentation of that profile as a two-binomial mixture. -/
theorem solution :
    (68 : ℝ) / 1000000 <
      Matrix.det (fun i j : Fin 3 => factorialMoment (i.val + j.val)) ∧
    ¬ ∃ a ∈ Set.Icc (0 : ℝ) 1, ∃ theta ∈ Set.Icc (0 : ℝ) 1,
      ∃ phi ∈ Set.Icc (0 : ℝ) 1,
        ∀ k : Fin 5, fourWeight k = a * binomialFour theta k + (1 - a) * binomialFour phi k := by
  have hdet : Matrix.det (fun i j : Fin 3 => factorialMoment (i.val + j.val)) =
      7354170493511 / 108000000000000000 := by
    rw [g53i_det_eq, g53i_fm0, g53i_fm1, g53i_fm2, g53i_fm3, g53i_fm4]; norm_num
  refine ⟨by rw [hdet]; norm_num, ?_⟩
  rintro ⟨a, -, t, -, u, -, h⟩
  have hm : ∀ j : ℕ, j ≤ 4 → factorialMoment j = a * t ^ j + (1 - a) * u ^ j := by
    intro j hj
    unfold factorialMoment
    simp only [h, binomialFour, Fin.sum_univ_five]
    interval_cases j <;> norm_num [Nat.choose] <;> ring
  have h0 := hdet
  rw [g53i_det_eq, hm 0 (by norm_num), hm 1 (by norm_num), hm 2 (by norm_num),
    hm 3 (by norm_num), hm 4 (by norm_num)] at h0
  have : (0:ℝ) = 7354170493511 / 108000000000000000 := by rw [← h0]; ring
  norm_num at this

end

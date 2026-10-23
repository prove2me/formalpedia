-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier18.P14.singletBellViolation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:44:28.022981+00:00
-- url     : https://prove2.me/submissions/5aa4f3bb-db8a-44ff-8679-bce190f6ee48

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P14
noncomputable section
open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Frontier18.P14

lemma x8_corr (a b : Fin 3 → ℝ) : singletCorrelation a b = -(∑ i, a i * b i) := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; push_cast; ring
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; positivity
  unfold singletCorrelation
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three, singlet,
    pauliDirection]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Complex.ext_iff]
  field_simp
  have h2' : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [h2']; ring

private lemma x8_cs (a u : Fin 3 → ℝ) (ha : ∑ i, a i ^ 2 = 1) :
    (∑ i, a i * u i) ^ 2 ≤ ∑ i, u i ^ 2 := by
  simp only [Fin.sum_univ_three] at *
  nlinarith [sq_nonneg (a 0 * u 1 - a 1 * u 0), sq_nonneg (a 0 * u 2 - a 2 * u 0),
    sq_nonneg (a 1 * u 2 - a 2 * u 1)]

theorem x8_main :
    (∑ ij : Fin 2 × Fin 2, Complex.normSq (singlet ij)) = 1 ∧
    (∀ a b : Fin 3 → ℝ, unitDirection a → unitDirection b →
      singletCorrelation a b = -(∑ i, a i * b i)) ∧
    (∀ a ap b bp : Fin 3 → ℝ,
      unitDirection a → unitDirection ap → unitDirection b → unitDirection bp →
      |chsh a ap b bp| ≤ 2 * Real.sqrt 2) ∧
    (∃ a ap b bp : Fin 3 → ℝ,
      unitDirection a ∧ unitDirection ap ∧ unitDirection b ∧ unitDirection bp ∧
      chsh a ap b bp = 2 * Real.sqrt 2) := by
  have h2' : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < Real.sqrt 2 := by positivity
  refine ⟨?_, fun a b _ _ => x8_corr a b, ?_, ?_⟩
  · simp only [Fintype.sum_prod_type, Fin.sum_univ_two, singlet]
    simp [Complex.normSq_apply]
    field_simp
    rw [h2']; norm_num
  · intro a ap b bp ha hap hb hbp
    unfold unitDirection at *
    simp only [chsh, x8_corr]
    set u : Fin 3 → ℝ := fun i => b i + bp i
    set v : Fin 3 → ℝ := fun i => b i - bp i
    have hx := x8_cs a u ha
    have hy := x8_cs ap v hap
    have hUV : ∑ i, u i ^ 2 + ∑ i, v i ^ 2 = 4 := by
      simp only [u, v, Fin.sum_univ_three] at *
      nlinarith
    have hS : -(∑ i, a i * b i) + -(∑ i, a i * bp i) + -(∑ i, ap i * b i) -
        -(∑ i, ap i * bp i) = -((∑ i, a i * u i) + (∑ i, ap i * v i)) := by
      simp only [u, v, Fin.sum_univ_three]; ring
    rw [hS, abs_neg]
    have h8 : ((∑ i, a i * u i) + (∑ i, ap i * v i)) ^ 2 ≤ 8 := by
      nlinarith [sq_nonneg ((∑ i, a i * u i) - (∑ i, ap i * v i))]
    have : 2 * Real.sqrt 2 = Real.sqrt 8 := by
      rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num),
        Real.sqrt_sq (by norm_num)]
    rw [this]
    exact Real.abs_le_sqrt h8
  · refine ⟨![1, 0, 0], ![0, 1, 0], ![-(1 / Real.sqrt 2), -(1 / Real.sqrt 2), 0],
      ![-(1 / Real.sqrt 2), 1 / Real.sqrt 2, 0], ?_, ?_, ?_, ?_, ?_⟩
    · simp [unitDirection, Fin.sum_univ_three]
    · simp [unitDirection, Fin.sum_univ_three]
    · simp [unitDirection, Fin.sum_univ_three, div_pow, h2']; norm_num
    · simp [unitDirection, Fin.sum_univ_three, div_pow, h2']; norm_num
    · simp only [chsh, x8_corr, Fin.sum_univ_three]
      simp
      field_simp
      nlinarith [h2']

end QAlgorithms.Papers.Independent.Frontier18.P14

open QAlgorithms.Papers.Independent.Frontier18.P14 in
theorem solution :
    (∑ ij : Fin 2 × Fin 2, Complex.normSq (singlet ij)) = 1 ∧
    (∀ a b : Fin 3 → ℝ, unitDirection a → unitDirection b →
      singletCorrelation a b = -(∑ i, a i * b i)) ∧
    (∀ a ap b bp : Fin 3 → ℝ,
      unitDirection a → unitDirection ap → unitDirection b → unitDirection bp →
      |chsh a ap b bp| ≤ 2 * Real.sqrt 2) ∧
    (∃ a ap b bp : Fin 3 → ℝ,
      unitDirection a ∧ unitDirection ap ∧ unitDirection b ∧ unitDirection bp ∧
      chsh a ap b bp = 2 * Real.sqrt 2) := x8_main

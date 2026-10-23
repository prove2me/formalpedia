-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P37.topologyResolvedPair
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-22T13:02:58.16212+00:00
-- url     : https://prove2.me/submissions/0e33a6f8-f796-4b47-a512-302c22c3b629

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P37

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Matrix ComplexConjugate Topology

namespace QAlgorithms.Papers.Independent.Information100.P37

lemma X7T_exp_unitary {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (hX : Xᴴ = -X) :
    NormedSpace.exp X * (NormedSpace.exp X)ᴴ = 1 ∧ (NormedSpace.exp X)ᴴ * NormedSpace.exp X = 1 := by
  rw [← Matrix.exp_conjTranspose, hX]
  constructor
  · rw [← Matrix.exp_add_of_commute _ _ (Commute.refl X).neg_right, add_neg_cancel,
      NormedSpace.exp_zero]
  · rw [← Matrix.exp_add_of_commute _ _ (Commute.refl X).neg_left, neg_add_cancel,
      NormedSpace.exp_zero]

lemma X7T_resp_rows {n : Type*} [Fintype n] [DecidableEq n] (U : Matrix n n ℂ)
    (h1 : U * Uᴴ = 1) (h2 : Uᴴ * U = 1) (i : n) :
    ∑ j, response U i j = 0 := by
  have hrow : ∀ k, ∑ j, transition U k j = 1 := by
    intro k
    have := congrArg Complex.re (congrFun (congrFun h1 k) k)
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq, Complex.one_re,
      Complex.re_sum] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [transition, Complex.normSq_apply, Complex.mul_re]
  have hcol : ∀ k, ∑ j, transition U j k = 1 := by
    intro k
    have := congrArg Complex.re (congrFun (congrFun h2 k) k)
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq, Complex.one_re,
      Complex.re_sum] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [transition, Complex.normSq_apply, Complex.mul_re]
  simp only [response, Matrix.sub_apply, Finset.sum_sub_distrib, Matrix.one_apply,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, hrow, mul_one, hcol]
  norm_num

lemma X7T_complete_unitary (t : ℝ) :
    walk (completeAdjacency 6) t * (walk (completeAdjacency 6) t)ᴴ = 1 ∧
    (walk (completeAdjacency 6) t)ᴴ * walk (completeAdjacency 6) t = 1 := by
  apply X7T_exp_unitary
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.neg_apply, completeAdjacency,
    smul_eq_mul]
  rw [Complex.real_smul, Complex.real_smul]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h, Complex.conj_ofReal]

end QAlgorithms.Papers.Independent.Information100.P37

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P37 in
theorem solution : ¬ (
    let tk := (5 / 6 : ℝ) * Real.arccos (3 * Real.sqrt 145 / 25 - 2)
    let UK := walk (completeAdjacency 6) tk
    let US := walk (starAdjacency 6) Real.pi
    cgp (conjSuperop UK) = 16 / 175 ∧ cgp (conjSuperop US) = 16 / 175 ∧
    cgpd (conjSuperop UK) = 16 * Real.sqrt 10 / 875 ∧ cgpd (conjSuperop US) = 4 * Real.sqrt 230 / 875 ∧
    cgpd (conjSuperop US) ^ 2 = (23 / 16 : ℝ) * cgpd (conjSuperop UK) ^ 2 ∧
    response UK = (96 / 125 : ℝ) • zeroSumProjector (Fin 6) ∧
    response US = (24 / 25 : ℝ) • leafProjector 6 ∧
    (∀ p : Fin 6 → ℝ, IsPopulation p →
      generated (conjSuperop UK) p = (96 / 125 : ℝ) * ((∑ j, p j ^ 2) - 1 / 6) ∧
      generated (conjSuperop US) p = (24 / 25 : ℝ) *
        ((∑ j : Fin 6, if j.val = 0 then 0 else p j ^ 2) -
          (∑ j : Fin 6, if j.val = 0 then 0 else p j) ^ 2 / 5))) := by
  intro h
  have h6 := h.2.2.2.2.2.1
  have hr := X7T_resp_rows _ (X7T_complete_unitary ((5 / 6 : ℝ) * Real.arccos (3 * Real.sqrt 145 / 25 - 2))).1
    (X7T_complete_unitary _).2 0
  rw [h6] at hr
  have hz : ∀ i j : Fin 6, zeroSumProjector (Fin 6) i j = 1 - 1 / 6 := fun i j => by
    show (1 : ℝ) - 1 / ((Fintype.card (Fin 6) : ℕ) : ℝ) = 1 - 1 / 6
    simp
  simp only [Matrix.smul_apply, hz, smul_eq_mul, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hr
  norm_num at hr

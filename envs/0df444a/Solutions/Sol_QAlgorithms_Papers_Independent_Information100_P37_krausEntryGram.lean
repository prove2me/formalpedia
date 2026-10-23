-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P37.krausEntryGram
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T11:25:05.201272+00:00
-- url     : https://prove2.me/submissions/93bd8e70-2097-47ff-a722-5350e91d7ae9

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P37

noncomputable section

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators Matrix ComplexConjugate Topology

namespace QAlgorithms.Papers.Independent.Information100.P37

lemma X7D_kraus_single {ι K : Type*} [Fintype ι] [DecidableEq ι] [Fintype K]
    (A : K → Matrix ι ι ℂ) (i l m : ι) :
    krausApply A (Matrix.single i i 1) l m = ∑ k, A k l i * conj (A k m i) := by
  simp only [krausApply, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.single_apply, RCLike.star_def]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single i] <;> simp +contextual [eq_comm]
  · intro b _ hb; simp [Ne.symm hb]
  · simp

end QAlgorithms.Papers.Independent.Information100.P37

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P37 in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {K : Type*} [Fintype K]
    (E : Superop ι ι) (hE : IsChannel E) (hu : E 1 = 1)
    (A : K → Matrix ι ι ℂ) (hA : IsKrausFamily A) (hrep : ∀ M, E M = krausApply A M) :
    ∀ i j, channelResponse E i j =
      (∑ l : ι, ∑ m : ι, if l = m then (0 : ℂ) else
        conj (∑ k, A k l i * conj (A k m i)) * (∑ r, A r l j * conj (A r m j))).re := by
  intro i j
  have hX : ∀ a l m, channelOutput E a l m =
      if l = m then 0 else ∑ k, A k l a * conj (A k m a) := by
    intro a l m
    simp only [channelOutput, offDiagonal, Matrix.sub_apply, Matrix.diagonal_apply,
      Matrix.diag, hrep, X7D_kraus_single]
    split_ifs with h <;> simp [h]
  have hc : ∀ a l m, conj (∑ k, A k l a * conj (A k m a)) = ∑ k, A k m a * conj (A k l a) := by
    intro a l m
    simp [map_sum, mul_comm]
  simp only [channelResponse, Matrix.trace, Matrix.diag, Matrix.mul_apply, hX, hc]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
  by_cases h : l = m
  · simp [h]
  · simp [h, Ne.symm h]

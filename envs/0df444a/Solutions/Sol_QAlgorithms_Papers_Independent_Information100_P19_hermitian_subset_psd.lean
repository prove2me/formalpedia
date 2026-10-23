-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P19.hermitian_subset_psd
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:16:04.10157+00:00
-- url     : https://prove2.me/submissions/62586113-fc0d-4f44-913f-bac179bb10c7

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19

open scoped BigOperators

namespace X7HermSubsetPsd
open QAlgorithms.Papers.Independent.Information100.P19

lemma pairing_sub_single {n : ℕ} (p q : Part n) (y : Part n → ℝ) :
    pairing (Finsupp.single p 1 - Finsupp.single q 1) y = y p - y q := by
  unfold pairing
  rw [Finsupp.sum_sub_index (fun _ _ _ => by ring)]
  rw [Finsupp.sum_single_index (by ring), Finsupp.sum_single_index (by ring)]
  ring

lemma pair_b11_b2 {d : ℕ} (x : Fin d → ℝ) :
    pairing (b11 - b2) (spectralMoments x) = (∑ i, x i) ^ 2 - ∑ i, x i ^ 2 := by
  exact (pairing_sub_single _ _ _).trans (by simp [spectralMoments, sq])

lemma pair_b31_b22 {d : ℕ} (x : Fin d → ℝ) :
    pairing (b31 - b22) (spectralMoments x) =
      (∑ i, x i ^ 3) * (∑ i, x i) - (∑ i, x i ^ 2) ^ 2 := by
  exact (pairing_sub_single _ _ _).trans (by simp [spectralMoments, sq])

lemma cs31 {d : ℕ} (x : Fin d → ℝ) (hx : ∀ i, 0 ≤ x i) :
    0 ≤ (∑ i, x i ^ 3) * (∑ i, x i) - (∑ i, x i ^ 2) ^ 2 := by
  have e : (∑ i, x i ^ 3) * (∑ i, x i) - (∑ i, x i ^ 2) ^ 2 =
      ∑ i, ∑ j, (x i ^ 3 * x j - x i ^ 2 * x j ^ 2) := by
    rw [sq, Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_sub_distrib]
  have e2 : 2 * ∑ i, ∑ j, (x i ^ 3 * x j - x i ^ 2 * x j ^ 2) =
      ∑ i, ∑ j, x i * x j * (x i - x j) ^ 2 := by
    rw [two_mul]
    conv_lhs => arg 2; rw [Finset.sum_comm]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  have h0 : 0 ≤ ∑ i, ∑ j, x i * x j * (x i - x j) ^ 2 :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
      mul_nonneg (mul_nonneg (hx i) (hx j)) (sq_nonneg _)))
  rw [e]; linarith

end X7HermSubsetPsd

open QAlgorithms.Papers.Independent.Information100.P19 X7HermSubsetPsd in
theorem solution (n : ℕ) (hn : 1 ≤ n) :
    allCone n ⊆ psdCone n ∧
    b11-b2 ∈ psdCone 2 ∧ b11-b2 ∉ allCone 2 ∧
    b31-b22 ∈ psdCone 4 ∧ b31-b22 ∉ allCone 4 := by
  refine ⟨fun f hf d hd x _ => hf d hd x, ?_, ?_, ?_, ?_⟩
  · intro d _ x hx
    rw [pair_b11_b2]
    have := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := x) (fun i _ => hx i)
    linarith
  · intro h
    have := h 2 (by norm_num) ![1, -1]
    rw [pair_b11_b2] at this
    norm_num [Fin.sum_univ_two] at this
  · intro d _ x hx
    rw [pair_b31_b22]; exact cs31 x hx
  · intro h
    have := h 2 (by norm_num) ![1, -1]
    rw [pair_b31_b22] at this
    norm_num [Fin.sum_univ_two] at this

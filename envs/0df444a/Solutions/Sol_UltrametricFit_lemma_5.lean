-- Prove2me | solution 1 for UltrametricFit.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:00:08.249455+00:00
-- url     : https://prove2.me/submissions/b5b5adc8-afa7-4ba0-bf0d-30e4e24463f9

import Mathlib
import Definitions.Def_UltrametricFit_avgDist

open UltrametricFit in
theorem solution {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : IsPseudometric d) (A B C : Finset (Fin n))
    (hA : A.Nonempty) (hB : B.Nonempty) (hC : C.Nonempty) :
    avgDist d A C ≤ avgDist d A B + avgDist d B C := by
  have key : (B.card : ℝ) * ∑ a ∈ A, ∑ c ∈ C, d a c ≤
      (C.card : ℝ) * ∑ a ∈ A, ∑ b ∈ B, d a b + (A.card : ℝ) * ∑ b ∈ B, ∑ c ∈ C, d b c := by
    calc (B.card : ℝ) * ∑ a ∈ A, ∑ c ∈ C, d a c = ∑ a ∈ A, ∑ c ∈ C, ∑ b ∈ B, d a c := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ a ∈ A, ∑ c ∈ C, ∑ b ∈ B, (d a b + d b c) :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun c _ =>
            Finset.sum_le_sum fun b _ => hd.triangle a c b
      _ = ∑ a ∈ A, ∑ c ∈ C, ∑ b ∈ B, d a b + ∑ a ∈ A, ∑ c ∈ C, ∑ b ∈ B, d b c := by
          simp only [Finset.sum_add_distrib]
      _ = (C.card : ℝ) * ∑ a ∈ A, ∑ b ∈ B, d a b + (A.card : ℝ) * ∑ b ∈ B, ∑ c ∈ C, d b c := by
          congr 1
          · rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [Finset.sum_const, nsmul_eq_mul]
          · rw [Finset.sum_const, nsmul_eq_mul, Finset.sum_comm]
  have ha : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hb : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
  have hc : (0 : ℝ) < C.card := by exact_mod_cast hC.card_pos
  unfold avgDist
  rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
  have := mul_le_mul_of_nonneg_left key
    (by positivity : (0 : ℝ) ≤ (A.card : ℝ) * B.card * C.card)
  nlinarith [this]

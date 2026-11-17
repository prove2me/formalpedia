-- Prove2me | solution 1 for QuantumLTF.Majority.krawtchouk_parseval
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-17T00:29:40.84243+00:00
-- url     : https://prove2.me/submissions/79c7527c-74ca-4547-ab33-a76294227f95

import Mathlib
import Definitions.Def_QuantumLTF_Majority_AdversaryModel
import Theorems.Thm_QuantumLTF_Majority_krawtchouk_weighted_orthogonality

open QuantumLTF.Majority

theorem solution : ∀ k : ℕ, ∀ r : Fin (k+1) → ℝ,
    (1/(2:ℝ)^k) * ∑ a : Fin (k+1), (k.choose a : ℝ) *
      (∑ t : Fin (k+1), (krawtchouk k t a : ℝ) * r t)^2 =
    ∑ t : Fin (k+1), (k.choose t : ℝ) * r t^2 := by
  classical
  intro k r
  simp_rw [pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.sum_comm]
  calc
    (∑ u : Fin (k + 1), ∑ a : Fin (k + 1),
        1 / (2 : ℝ) ^ k *
          ((k.choose a : ℝ) * ((krawtchouk k t a : ℝ) * r t *
            ((krawtchouk k u a : ℝ) * r u)))) =
        ∑ u : Fin (k + 1),
          if t = u then (k.choose t : ℝ) * (r t * r t) else 0 := by
      apply Finset.sum_congr rfl
      intro u hu
      calc
        (∑ a : Fin (k + 1),
            1 / (2 : ℝ) ^ k *
              ((k.choose a : ℝ) * ((krawtchouk k t a : ℝ) * r t *
                ((krawtchouk k u a : ℝ) * r u)))) =
            (1 / (2 : ℝ) ^ k * (r t * r u)) *
              ∑ a : Fin (k + 1), (k.choose a : ℝ) *
                (krawtchouk k t a : ℝ) * (krawtchouk k u a : ℝ) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro a ha
              ring
        _ = if t = u then (k.choose t : ℝ) * (r t * r t) else 0 := by
              rw [krawtchouk_weighted_orthogonality k t u]
              by_cases htu : t = u
              · subst u
                simp only [if_pos rfl]
                have hpow : (2 : ℝ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
                field_simp
                simp
                ring
              · simp [htu]
    _ = (k.choose t : ℝ) * (r t * r t) := by simp


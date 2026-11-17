-- Prove2me | solution 1 for QuantumLTF.Majority.lemma_4_2_two_channel
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-16T18:14:52.766637+00:00
-- url     : https://prove2.me/submissions/846def63-5781-437a-9b2b-c3060ae49a71

import Mathlib
import Definitions.Def_QuantumLTF_Majority_AdversaryModel
import Theorems.Thm_QuantumLTF_Majority_krawtchouk_weighted_orthogonality

open QuantumLTF.Majority

theorem solution : ∀ k : ℕ, ∀ p q : Fin (k+1) → ℝ,
    let P : Fin (k+1) → ℝ := fun a =>
      ∑ t : Fin (k+1), (krawtchouk k t a : ℝ) * p t
    let Q : Fin (k+1) → ℝ := fun a =>
      ∑ t : Fin (k+1), (krawtchouk k t a : ℝ) * ((-1 : ℝ) ^ (t : ℕ) * q t)
    (1/(2:ℝ)^k) * ∑ a : Fin (k+1), (k.choose a : ℝ) * (P a^2 + Q a^2) =
      ∑ t : Fin (k+1), (k.choose t : ℝ) * (p t^2+q t^2) := by
  classical
  intro k p q
  dsimp only
  have hparseval (r : Fin (k + 1) → ℝ) :
      (1 / (2 : ℝ) ^ k) *
          ∑ a : Fin (k + 1), (k.choose a : ℝ) *
            (∑ t : Fin (k + 1), (krawtchouk k t a : ℝ) * r t) ^ 2 =
        ∑ t : Fin (k + 1), (k.choose t : ℝ) * r t ^ 2 := by
    simp_rw [pow_two, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.sum_comm]
    calc
      (∑ u : Fin (k + 1), ∑ a : Fin (k + 1),
          1 / (2 : ℝ) ^ k *
            ((k.choose a : ℝ) *
              ((krawtchouk k t a : ℝ) * r t *
                ((krawtchouk k u a : ℝ) * r u)))) =
          ∑ u : Fin (k + 1),
            if t = u then (k.choose t : ℝ) * (r t * r t) else 0 := by
        apply Finset.sum_congr rfl
        intro u hu
        calc
          (∑ a : Fin (k + 1),
              1 / (2 : ℝ) ^ k *
                ((k.choose a : ℝ) *
                  ((krawtchouk k t a : ℝ) * r t *
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
  rw [Finset.mul_sum]
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, hparseval p]
  rw [← Finset.mul_sum, hparseval (fun t => (-1 : ℝ) ^ (t : ℕ) * q t)]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  simp only [mul_pow]
  rw [show ((-1 : ℝ) ^ (t : ℕ)) ^ 2 = 1 by
    rw [← pow_mul]
    norm_num]
  ring


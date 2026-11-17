-- Prove2me | solution 1 for QuantumLTF.Majority.intersectionTransform_parseval_of_cross_zero
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-17T00:38:25.900362+00:00
-- url     : https://prove2.me/submissions/fc6a85d4-a872-417d-84ce-a39f4c21392f

import Mathlib
import Definitions.Def_QuantumLTF_Majority_AdversaryModel
import Theorems.Thm_QuantumLTF_Majority_krawtchouk_parseval

open QuantumLTF.Majority

theorem solution : ∀ k : ℕ, ∀ p q : Fin (k+1) → ℝ,
    (∑ t : Fin (k+1), (k.choose t : ℝ) *
      ((-1 : ℝ) ^ (t : ℕ) * p t * q t)) = 0 →
    (1/(2:ℝ)^k) * ∑ a : Fin (k+1), (k.choose a : ℝ) *
      (intersectionTransform k p q a)^2 =
    ∑ t : Fin (k+1), (k.choose t : ℝ) * (p t^2+q t^2) := by
  classical
  intro k p q hcross
  unfold intersectionTransform
  rw [krawtchouk_parseval k
    (fun t => p t + (-1 : ℝ) ^ (t : ℕ) * q t)]
  calc
    (∑ t : Fin (k + 1), (k.choose t : ℝ) *
        (p t + (-1 : ℝ) ^ (t : ℕ) * q t) ^ 2) =
      (∑ t : Fin (k + 1), (k.choose t : ℝ) * (p t ^ 2 + q t ^ 2)) +
        2 * ∑ t : Fin (k + 1), (k.choose t : ℝ) *
          ((-1 : ℝ) ^ (t : ℕ) * p t * q t) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro t ht
      have hsign : ((-1 : ℝ) ^ (t : ℕ)) ^ 2 = 1 := by
        rw [← pow_mul]
        norm_num
      calc
        (k.choose t : ℝ) * (p t + (-1 : ℝ) ^ (t : ℕ) * q t) ^ 2 =
            (k.choose t : ℝ) *
              (p t ^ 2 + 2 * ((-1 : ℝ) ^ (t : ℕ)) * p t * q t +
                (((-1 : ℝ) ^ (t : ℕ)) ^ 2) * q t ^ 2) := by ring
        _ = (k.choose t : ℝ) * (p t ^ 2 + q t ^ 2) +
            2 * ((k.choose t : ℝ) *
              ((-1 : ℝ) ^ (t : ℕ) * p t * q t)) := by
              rw [hsign]
              ring
    _ = ∑ t : Fin (k + 1), (k.choose t : ℝ) * (p t ^ 2 + q t ^ 2) := by
      rw [hcross]
      ring


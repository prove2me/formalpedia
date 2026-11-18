-- Prove2me | solution 1 for QuantumLTF.Majority.rank_one_dual_of_separated_moments
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-17T15:43:31.7102+00:00
-- url     : https://prove2.me/submissions/bfb9dee4-34c9-42f5-ac4a-dd4ca73e24a8

import Mathlib
import Definitions.Def_QuantumLTF_Majority_AdversaryModel
import Theorems.Thm_QuantumLTF_Majority_intersection_rank_one_posSemidef

open QAlgorithms
open QuantumLTF.Majority

theorem solution : ∀ n r : ℕ, ∀ L U : Fin (r+1) → ℝ,
    (∀ A B : ExactSupports n r, A ≠ B →
      (∑ S : Qubits n, if majorityBit A.1 S ≠ majorityBit B.1 S then
        (2:ℝ)^(-n:ℤ) * L (intersectionIndex A S) * L (intersectionIndex B S) else 0) = 0) →
    (∀ A B : ExactSupports n r, A ≠ B →
      (∑ S : Qubits n, if majorityBit A.1 S ≠ majorityBit B.1 S then
        (2:ℝ)^(-n:ℤ) * U (intersectionIndex A S) * U (intersectionIndex B S) else 0) = 0) →
    (∀ A B : ExactSupports n r, A ≠ B →
      (∑ S : Qubits n, if majorityBit A.1 S ≠ majorityBit B.1 S then
        (2:ℝ)^(-n:ℤ) * L (intersectionIndex A S) * U (intersectionIndex B S) else 0) = 1/2) →
    (∀ A B : ExactSupports n r, A ≠ B →
      (∑ S : Qubits n, if majorityBit A.1 S ≠ majorityBit B.1 S then
        (2:ℝ)^(-n:ℤ) * U (intersectionIndex A S) * L (intersectionIndex B S) else 0) = 1/2) →
    let W := fun a => L a + U a
    let X : Qubits n → Matrix (ExactSupports n r) (ExactSupports n r) ℝ :=
      fun S A B => (2:ℝ)^(-n:ℤ) * W (intersectionIndex A S) * W (intersectionIndex B S)
    DualFeasible (fun A : ExactSupports n r => A.1) X := by
  intro n r L U hLL hUU hLU hUL
  dsimp only
  constructor
  · intro S
    exact intersection_rank_one_posSemidef n r (fun a => L a + U a) S
  · intro A B hAB
    have hsplit :
        (∑ S : Qubits n, if majorityBit A.1 S ≠ majorityBit B.1 S then
          (2:ℝ)^(-n:ℤ) * (L (intersectionIndex A S) + U (intersectionIndex A S)) *
            (L (intersectionIndex B S) + U (intersectionIndex B S)) else 0) =
        (∑ S : Qubits n, if majorityBit A.1 S ≠ majorityBit B.1 S then
          (2:ℝ)^(-n:ℤ) * L (intersectionIndex A S) * L (intersectionIndex B S) else 0) +
        (∑ S : Qubits n, if majorityBit A.1 S ≠ majorityBit B.1 S then
          (2:ℝ)^(-n:ℤ) * L (intersectionIndex A S) * U (intersectionIndex B S) else 0) +
        (∑ S : Qubits n, if majorityBit A.1 S ≠ majorityBit B.1 S then
          (2:ℝ)^(-n:ℤ) * U (intersectionIndex A S) * L (intersectionIndex B S) else 0) +
        (∑ S : Qubits n, if majorityBit A.1 S ≠ majorityBit B.1 S then
          (2:ℝ)^(-n:ℤ) * U (intersectionIndex A S) * U (intersectionIndex B S) else 0) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro S _
      split_ifs <;> ring
    rw [hsplit, hLL A B hAB, hLU A B hAB, hUL A B hAB, hUU A B hAB]
    norm_num

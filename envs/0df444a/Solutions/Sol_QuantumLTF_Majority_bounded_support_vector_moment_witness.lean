-- Prove2me | solution 1 for QuantumLTF.Majority.bounded_support_vector_moment_witness
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-17T16:57:05.130928+00:00
-- url     : https://prove2.me/submissions/000e5712-45ff-4b60-ba0e-c6355cc22602
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_QuantumLTF_Majority_AdversaryModel
import Theorems.Thm_QuantumLTF_Majority_bounded_support_vector_coefficient_witness
import Theorems.Thm_QuantumLTF_Majority_normalized_intersection_sum

open QAlgorithms
open QuantumLTF.Majority

theorem solution : ∃ C : ℝ, 0 < C ∧ ∀ n k : ℕ, 2 ≤ k → k ≤ n →
    ∃ d : ℕ, ∃ W : ℕ → ℕ → Fin d → ℝ,
      (∀ A B : BoundedSupports n k, A ≠ B →
        (∑ S : Qubits n, if majorityBit A.1 S ≠ majorityBit B.1 S then
          (2:ℝ)^(-n:ℤ) * ∑ j : Fin d,
            W A.1.card ((A.1.filter fun i => S i).card) j *
            W B.1.card ((B.1.filter fun i => S i).card) j else 0) = 1) ∧
      (∀ A : BoundedSupports n k,
        ∑ S : Qubits n, (2:ℝ)^(-n:ℤ) * ∑ j : Fin d,
          (W A.1.card ((A.1.filter fun i => S i).card) j)^2 ≤ C * Real.log k) := by
  obtain ⟨C, hC, hwit⟩ := bounded_support_vector_coefficient_witness
  refine ⟨C, hC, ?_⟩
  intro n k hk hkn
  obtain ⟨d, W, hmom, henergy⟩ := hwit n k hk hkn
  refine ⟨d, W, hmom, ?_⟩
  intro A
  let r := A.1.card
  let E : ExactSupports n r := ⟨A.1, rfl⟩
  let f : Fin (r + 1) → ℝ := fun a => ∑ j : Fin d, (W r a j)^2
  have hrn : r ≤ n := by
    dsimp [r]
    simpa using A.1.card_le_univ
  have hr1 : 1 ≤ r := by
    dsimp [r]
    exact A.2.1.card_pos
  have hrk : r ≤ k := by exact A.2.2
  have hnorm := normalized_intersection_sum n r hrn E f
  have hrewrite :
      (∑ S : Qubits n, (2:ℝ)^(-n:ℤ) * ∑ j : Fin d,
        (W A.1.card ((A.1.filter fun i => S i).card) j)^2) =
      (1/(2:ℝ)^r) * ∑ a : Fin (r+1), (r.choose a : ℝ) * ∑ j : Fin d, (W r a j)^2 := by
    rw [← hnorm]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S _
    rfl
  rw [hrewrite]
  exact henergy r hr1 hrk

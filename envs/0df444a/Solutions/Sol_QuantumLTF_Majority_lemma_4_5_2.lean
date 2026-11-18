-- Prove2me | solution 2 for QuantumLTF.Majority.lemma_4_5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-17T16:46:47.060553+00:00
-- url     : https://prove2.me/submissions/2b14e57a-214c-4c35-822a-f7daa07b2080
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_QuantumLTF_Majority_AdversaryModel
import Theorems.Thm_QuantumLTF_Majority_bounded_gram_dual_of_moment_identity
import Theorems.Thm_QuantumLTF_Majority_bounded_support_vector_moment_witness

open QAlgorithms
open QuantumLTF.Majority

theorem solution : ∃ C : ℝ, 0 < C ∧ ∀ n k : ℕ, 2 ≤ k → k ≤ n →
    ∃ X : Qubits n → Matrix (BoundedSupports n k) (BoundedSupports n k) ℝ,
      DualFeasible (fun A : BoundedSupports n k => A.1) X ∧
      DualCostAtMost X (C * Real.log k) := by
  obtain ⟨C, hC, hwit⟩ := bounded_support_vector_moment_witness
  refine ⟨C, hC, ?_⟩
  intro n k hk hkn
  obtain ⟨d, W, hmom, hcost⟩ := hwit n k hk hkn
  let X : Qubits n → Matrix (BoundedSupports n k) (BoundedSupports n k) ℝ :=
    fun S A B => (2:ℝ)^(-n:ℤ) * ∑ j : Fin d,
      W A.1.card ((A.1.filter fun i => S i).card) j *
      W B.1.card ((B.1.filter fun i => S i).card) j
  refine ⟨X, ?_, ?_⟩
  · simpa [X] using bounded_gram_dual_of_moment_identity n k d W hmom
  · intro A
    simpa [X, pow_two, mul_assoc] using hcost A

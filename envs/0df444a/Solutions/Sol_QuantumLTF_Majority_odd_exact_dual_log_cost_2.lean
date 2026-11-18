-- Prove2me | solution 2 for QuantumLTF.Majority.odd_exact_dual_log_cost
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-17T15:46:02.15741+00:00
-- url     : https://prove2.me/submissions/1c28e5fe-8c57-454d-8dca-bf31061c3301
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_QuantumLTF_Majority_AdversaryModel
import Theorems.Thm_QuantumLTF_Majority_rank_one_dual_of_separated_moments
import Theorems.Thm_QuantumLTF_Majority_odd_separated_krawtchouk_witness

open QAlgorithms
open QuantumLTF.Majority

theorem solution : ∃ C : ℝ, 0 < C ∧ ∀ n r : ℕ, 3 ≤ r → r ≤ n → Odd r →
    ∃ X : Qubits n → Matrix (ExactSupports n r) (ExactSupports n r) ℝ,
      DualFeasible (fun A : ExactSupports n r => A.1) X ∧
      DualCostAtMost X (C * Real.log r) := by
  obtain ⟨C, hC, hwit⟩ := odd_separated_krawtchouk_witness
  refine ⟨C, hC, ?_⟩
  intro n r hr hrn hodd
  obtain ⟨L, U, hLL, hUU, hLU, hUL, hcost⟩ := hwit n r hr hrn hodd
  let W : Fin (r + 1) → ℝ := fun a => L a + U a
  let X : Qubits n → Matrix (ExactSupports n r) (ExactSupports n r) ℝ :=
    fun S A B => (2:ℝ)^(-n:ℤ) * W (intersectionIndex A S) * W (intersectionIndex B S)
  refine ⟨X, ?_, ?_⟩
  · simpa [W, X] using
      (rank_one_dual_of_separated_moments n r L U hLL hUU hLU hUL)
  · intro A
    simpa [X, W, pow_two, mul_assoc] using hcost A

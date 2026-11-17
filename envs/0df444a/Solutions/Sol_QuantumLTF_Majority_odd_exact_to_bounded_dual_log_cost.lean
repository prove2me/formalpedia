-- Prove2me | solution 1 for QuantumLTF.Majority.odd_exact_to_bounded_dual_log_cost
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-17T00:54:29.676469+00:00
-- url     : https://prove2.me/submissions/3cf128ee-3cbc-4131-986d-75afa781fa18
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_QuantumLTF_Majority_AdversaryModel
import Theorems.Thm_QuantumLTF_Majority_odd_exact_family_to_all_sizes
import Theorems.Thm_QuantumLTF_Majority_assemble_exact_support_duals

open QAlgorithms
open QuantumLTF.Majority

theorem solution : ∀ C₀ : ℝ, 0 < C₀ →
    (∀ n r : ℕ, 3 ≤ r → r ≤ n → Odd r →
      ∃ X : Qubits n → Matrix (ExactSupports n r) (ExactSupports n r) ℝ,
        DualFeasible (fun A : ExactSupports n r => A.1) X ∧
        DualCostAtMost X (C₀ * Real.log r)) →
    ∃ C : ℝ, 0 < C ∧ ∀ n k : ℕ, 2 ≤ k → k ≤ n →
      ∃ X : Qubits n → Matrix (BoundedSupports n k) (BoundedSupports n k) ℝ,
        DualFeasible (fun A : BoundedSupports n k => A.1) X ∧
        DualCostAtMost X (C * Real.log k) := by
  intro C₀ hC₀ hodd
  obtain ⟨C₁, hC₁, hall⟩ := odd_exact_family_to_all_sizes C₀ hC₀ hodd
  exact assemble_exact_support_duals C₁ hC₁ hall


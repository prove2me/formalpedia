-- Prove2me | solution 1 for QuantumLTF.Majority.lemma_4_5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-17T00:19:41.768876+00:00
-- url     : https://prove2.me/submissions/9b139285-6ad1-4682-9a41-7bd9d220b44e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_QuantumLTF_Majority_AdversaryModel
import Theorems.Thm_QuantumLTF_Majority_odd_exact_dual_log_cost
import Theorems.Thm_QuantumLTF_Majority_odd_exact_to_bounded_dual_log_cost

open QAlgorithms
open QuantumLTF.Majority

theorem solution : ∃ C : ℝ, 0<C ∧ ∀ n k : ℕ, 2≤k → k≤n →
    ∃ X : Qubits n → Matrix (BoundedSupports n k) (BoundedSupports n k) ℝ,
      DualFeasible (fun A : BoundedSupports n k => A.1) X ∧
      DualCostAtMost X (C*Real.log k) := by
  obtain ⟨C₀, hC₀, hodd⟩ := odd_exact_dual_log_cost
  exact odd_exact_to_bounded_dual_log_cost C₀ hC₀ hodd


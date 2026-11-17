-- Prove2me | solution 1 for QuantumLTF.Majority.odd_exact_dual_log_cost
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-17T00:37:07.744135+00:00
-- url     : https://prove2.me/submissions/5accaa54-14ed-44b3-b103-4e10a06e9391
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_QuantumLTF_Majority_AdversaryModel
import Theorems.Thm_QuantumLTF_Majority_odd_krawtchouk_polynomial_witness
import Theorems.Thm_QuantumLTF_Majority_exact_support_dual_from_krawtchouk_witness

open QAlgorithms
open QuantumLTF.Majority

theorem solution : ∃ C : ℝ, 0 < C ∧ ∀ n r : ℕ, 3 ≤ r → r ≤ n → Odd r →
    ∃ X : Qubits n → Matrix (ExactSupports n r) (ExactSupports n r) ℝ,
      DualFeasible (fun A : ExactSupports n r => A.1) X ∧
      DualCostAtMost X (C * Real.log r) := by
  obtain ⟨C, hC, hwitness⟩ := odd_krawtchouk_polynomial_witness
  refine ⟨C, hC, ?_⟩
  intro n r hr hrn hodd
  obtain ⟨p, q, hnorm, hsupp, hcross, henergy⟩ := hwitness r hr hodd
  exact exact_support_dual_from_krawtchouk_witness n r hr hrn p q hnorm hsupp
    hcross (C * Real.log r) henergy


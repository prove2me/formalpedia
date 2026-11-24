-- Prove2me | solution 1 for QuantumLTF.Majority.compile_bounded_support_dual
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-23T22:00:15.319064+00:00
-- url     : https://prove2.me/submissions/1fd2a3f3-4a08-4f22-a8ed-5c0a9351dfba

import Theorems.Thm_compiler_abstract_adversary_identification
import Theorems.Thm_QuantumLTF_Majority_realize_phase_clock_algorithm

open QAlgorithms QuantumLTF.Membership QuantumLTF.Majority

theorem solution : ∃ K : ℝ, 0 < K ∧ ∀ n k : ℕ, 2 ≤ k → k ≤ n →
    ∀ T : ℝ, 0 ≤ T →
    ∀ X : Qubits n → Matrix (BoundedSupports n k) (BoundedSupports n k) ℝ,
      DualFeasible (fun A : BoundedSupports n k => A.1) X → DualCostAtMost X T →
      ∃ (m : ℕ) (c : OracleCircuit gates12 (fun _ : Fin 1 => n+1) m)
        (out : Fin n ↪ Fin m),
        (c.queryCount 0 : ℝ) ≤ K * (T+1) ∧ LearnsUpTo (k:=k) c out (2/3) := by
  refine ⟨73, by norm_num, ?_⟩
  intro n k _ _ T hT X hX hcost
  obtain ⟨ω, hω, N, hN, hbound, U, hU⟩ :=
    compiler_abstract_adversary_identification
      (fun (A : BoundedSupports n k) S => majorityBit A.1 S) X hX.1 hX.2 T hT hcost
  letI : Fintype ω := hω
  obtain ⟨m, c, out, hqueries, hlearns⟩ :=
    realize_phase_clock_algorithm n k N ω hN U hU
  refine ⟨m, c, out, ?_, hlearns⟩
  exact (by exact_mod_cast hqueries : (c.queryCount 0 : ℝ) ≤ (N : ℝ)).trans hbound

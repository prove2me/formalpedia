-- Prove2me | solution 1 for QuantumLTF.Membership.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-14T20:39:11.894051+00:00
-- url     : https://prove2.me/submissions/1648dc8d-bb49-40f4-91bf-24bfbc7abd51

import Theorems.Thm_QuantumLTF_Membership_centerPhase_factorization

open QAlgorithms QuantumLTF.Membership

theorem solution (b : ℕ) :
    ∃ u : Fin b → Matrix Bool Bool ℂ, (∀ i, u i ∈ Matrix.unitaryGroup Bool ℂ) ∧
      gridQFT b = tensorSingle u * qftQubits b * tensorSingle u := by
  refine ⟨centerPhaseGate b, ?_⟩
  exact centerPhase_factorization b

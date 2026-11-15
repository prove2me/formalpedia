-- Prove2me | solution 1 for QuantumLTF.Membership.centerPhase_factorization
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-14T21:25:37.72459+00:00
-- url     : https://prove2.me/submissions/d678f007-c44a-4cc6-98a3-a425006b2dc8

import Theorems.Thm_QuantumLTF_Membership_centerPhaseGate_unitary
import Theorems.Thm_QuantumLTF_Membership_centerPhase_matrix_identity

open QAlgorithms

theorem solution (b : ℕ) :
    (∀ i : Fin b,
      QuantumLTF.Membership.centerPhaseGate b i ∈ Matrix.unitaryGroup Bool ℂ) ∧
      gridQFT b =
        QuantumLTF.Membership.tensorSingle
            (QuantumLTF.Membership.centerPhaseGate b) *
          qftQubits b *
        QuantumLTF.Membership.tensorSingle
            (QuantumLTF.Membership.centerPhaseGate b) := by
  constructor
  · exact QuantumLTF.Membership.centerPhaseGate_unitary b
  · exact QuantumLTF.Membership.centerPhase_matrix_identity b

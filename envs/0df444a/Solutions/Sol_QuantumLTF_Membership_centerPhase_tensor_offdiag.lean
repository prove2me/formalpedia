-- Prove2me | solution 1 for QuantumLTF.Membership.centerPhase_tensor_offdiag
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-15T00:02:14.209135+00:00
-- url     : https://prove2.me/submissions/1cd49180-3b15-4ec6-a201-698366901f6c

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Membership_tensorSingle
import Definitions.Def_QuantumLTF_Membership_centerPhaseGate
import Theorems.Thm_QuantumLTF_Membership_tensorSingle_offdiag

open QAlgorithms

theorem solution {b : ℕ} (y z : Qubits b) (hyz : y ≠ z) :
    QuantumLTF.Membership.tensorSingle
      (QuantumLTF.Membership.centerPhaseGate b) y z = 0 := by
  apply QuantumLTF.Membership.tensorSingle_offdiag _ _ y z hyz
  intro i a d had
  simp [QuantumLTF.Membership.centerPhaseGate, had]

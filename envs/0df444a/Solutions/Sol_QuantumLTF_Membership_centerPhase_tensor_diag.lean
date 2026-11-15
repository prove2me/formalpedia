-- Prove2me | solution 1 for QuantumLTF.Membership.centerPhase_tensor_diag
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-15T02:17:24.495794+00:00
-- url     : https://prove2.me/submissions/1add29b5-4c37-44b1-bc23-14583cca8e76

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Membership_tensorSingle
import Definitions.Def_QuantumLTF_Membership_centerPhaseGate
import Theorems.Thm_QuantumLTF_Membership_centerPhase_exponent_sum

open QAlgorithms

theorem solution (b : ℕ) (z : Qubits b) :
    let N : ℂ := (2 : ℂ) ^ b
    let c : ℂ := -(1 / 2) + 1 / (2 * N)
    QuantumLTF.Membership.tensorSingle
        (QuantumLTF.Membership.centerPhaseGate b) z z =
      Complex.exp (2 * Real.pi * Complex.I *
        (c * (bitsToNat z : ℂ) + N * c ^ 2 / 2)) := by
  dsimp
  rw [QuantumLTF.Membership.tensorSingle, Matrix.of_apply]
  simp only [QuantumLTF.Membership.centerPhaseGate, Matrix.of_apply, if_pos]
  rw [← Complex.exp_sum]
  apply congrArg Complex.exp
  rw [← Finset.mul_sum]
  convert congrArg (fun x : ℂ => 2 * Real.pi * Complex.I * x)
    (QuantumLTF.Membership.centerPhase_exponent_sum b z) using 1 <;>
    norm_num <;> ring
  apply Finset.sum_congr rfl
  intro i _
  split <;> norm_num <;> ring

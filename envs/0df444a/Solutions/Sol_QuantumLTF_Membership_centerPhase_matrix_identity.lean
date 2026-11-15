-- Prove2me | solution 1 for QuantumLTF.Membership.centerPhase_matrix_identity
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-15T02:34:57.5332+00:00
-- url     : https://prove2.me/submissions/ec2dbf59-775e-4b0d-a576-2f4853923c0e

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Fourier
import Definitions.Def_QAlgorithms_Defs_GradientMethods
import Definitions.Def_QuantumLTF_Membership_tensorSingle
import Definitions.Def_QuantumLTF_Membership_centerPhaseGate
import Theorems.Thm_Matrix_diagonal_sandwich_apply
import Theorems.Thm_QuantumLTF_Membership_centerPhase_tensor_offdiag
import Theorems.Thm_QuantumLTF_Membership_centerPhase_tensor_diag
import Theorems.Thm_QuantumLTF_Membership_centered_product_expand

open QAlgorithms

theorem solution (b : ℕ) :
    gridQFT b =
      QuantumLTF.Membership.tensorSingle
          (QuantumLTF.Membership.centerPhaseGate b) *
        qftQubits b *
      QuantumLTF.Membership.tensorSingle
          (QuantumLTF.Membership.centerPhaseGate b) := by
  let D := QuantumLTF.Membership.tensorSingle
    (QuantumLTF.Membership.centerPhaseGate b)
  ext y z
  rw [Matrix.diagonal_sandwich_apply D (qftQubits b)
    (fun x t h => QuantumLTF.Membership.centerPhase_tensor_offdiag x t h)]
  dsimp [D]
  rw [QuantumLTF.Membership.centerPhase_tensor_diag]
  rw [QuantumLTF.Membership.centerPhase_tensor_diag]
  simp only [gridQFT, gridPoint, qftQubits, qftMatrix,
    Matrix.of_apply, Matrix.submatrix_apply, bitsEquivFin_apply]
  let N : ℂ := (2 : ℂ) ^ b
  let c : ℂ := -(1 / 2) + 1 / (2 * N)
  have hN : N ≠ 0 := pow_ne_zero _ (by norm_num)
  have hphase := QuantumLTF.Membership.centered_product_expand
    N (bitsToNat y : ℂ) (bitsToNat z : ℂ) c hN
  dsimp [N, c] at hphase ⊢
  generalize hpy : (2 * Real.pi * Complex.I *
    ((-(1 / 2) + 1 / (2 * (2 : ℂ) ^ b)) * (bitsToNat y : ℂ) +
      (2 : ℂ) ^ b * (-(1 / 2) + 1 / (2 * (2 : ℂ) ^ b)) ^ 2 / 2)) = py
  generalize hpz : (2 * Real.pi * Complex.I *
    ((-(1 / 2) + 1 / (2 * (2 : ℂ) ^ b)) * (bitsToNat z : ℂ) +
      (2 : ℂ) ^ b * (-(1 / 2) + 1 / (2 * (2 : ℂ) ^ b)) ^ 2 / 2)) = pz
  generalize hpq : ((2 * Real.pi * Complex.I *
    ((bitsToNat y * bitsToNat z : ℕ) : ℂ)) / ((2 ^ b : ℕ) : ℂ)) = pq
  generalize hsdef : ((Real.sqrt (2 ^ b : ℕ) : ℂ)) = s
  have hs : ((Real.sqrt ((2 : ℝ) ^ b))⁻¹ : ℂ) = s⁻¹ := by
    rw [← hsdef]
    norm_num
  rw [hs]
  rw [show Complex.exp py * (Complex.exp pq / s) * Complex.exp pz =
      (Complex.exp py * Complex.exp pq * Complex.exp pz) * s⁻¹ by
        rw [div_eq_mul_inv]
        ring]
  rw [← Complex.exp_add, ← Complex.exp_add]
  apply congrArg (fun q : ℂ => q * s⁻¹)
  apply congrArg Complex.exp
  rw [← hpy, ← hpq, ← hpz]
  norm_num at hphase ⊢
  have hscaled := congrArg (fun t : ℂ => 2 * Real.pi * Complex.I * t) hphase
  convert hscaled using 1 <;> ring

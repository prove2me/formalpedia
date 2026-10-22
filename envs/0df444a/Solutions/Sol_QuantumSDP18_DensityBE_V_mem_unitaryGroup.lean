-- Prove2me | solution 1 for QuantumSDP18.DensityBE.V_mem_unitaryGroup
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:03:27.631914+00:00
-- url     : https://prove2.me/submissions/b5608ff6-72b0-49a6-9267-a88377a968b9

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BlockEncoding
import Definitions.Def_QuantumSDP18_DensityBE_Setting

set_option autoImplicit false
open scoped Kronecker ComplexOrder
open QuantumSDP18.DensityBE

lemma perm_unitary {α : Type*} [Fintype α] [DecidableEq α] (e : α ≃ α) :
    (Matrix.of fun x y => if x = e y then (1 : ℂ) else 0) ∈ Matrix.unitaryGroup α ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext a b
  simp only [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (e.symm a)]
  · by_cases h : a = b <;> simp [h, eq_comm]
  · intro y _ hy
    have : a ≠ e y := fun h => hy (by rw [h]; simp)
    simp [this]
  · simp

theorem solution {w c : ℕ} (G : Matrix (Reg w c) (Reg w c) ℂ)
    (hG : G ∈ Matrix.unitaryGroup (Reg w c) ℂ) :
    V G ∈ Matrix.unitaryGroup (Big w c) ℂ := by
  have h1 : ((1 : Matrix (QAlgorithms.Qubits w × Bool) (QAlgorithms.Qubits w × Bool) ℂ) ⊗ₖ G)
      ∈ Matrix.unitaryGroup (Big w c) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff] at hG ⊢
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      ← Matrix.mul_kronecker_mul, mul_one, ← Matrix.star_eq_conjTranspose, hG,
      Matrix.one_kronecker_one]
  have h2 : ((1 : Matrix (QAlgorithms.Qubits w × Bool) (QAlgorithms.Qubits w × Bool) ℂ) ⊗ₖ
      G.conjTranspose) = star ((1 : Matrix (QAlgorithms.Qubits w × Bool)
        (QAlgorithms.Qubits w × Bool) ℂ) ⊗ₖ G) := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
  have h3 : swapReg w c ∈ Matrix.unitaryGroup (Big w c) ℂ := perm_unitary (swapEquiv w c)
  unfold V
  rw [h2]
  exact Submonoid.mul_mem _ (Submonoid.mul_mem _ (Unitary.star_mem h1) h3) h1

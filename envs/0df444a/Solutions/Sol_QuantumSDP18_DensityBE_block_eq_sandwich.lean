-- Prove2me | solution 1 for QuantumSDP18.DensityBE.block_eq_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:03:56.655925+00:00
-- url     : https://prove2.me/submissions/7f30a4dd-70de-4e79-b3a3-da3f0290796f

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BlockEncoding
import Definitions.Def_QuantumSDP18_DensityBE_Setting

set_option autoImplicit false
open scoped Kronecker ComplexOrder
open QuantumSDP18.DensityBE

lemma gen_entry {X R : Type*} [Fintype X] [Fintype R] [DecidableEq X] [DecidableEq R]
    (G : Matrix R R ℂ) (S : Matrix (X × R) (X × R) ℂ) (z : R) (a b : X) :
    (((1 : Matrix X X ℂ) ⊗ₖ G.conjTranspose) * S * ((1 : Matrix X X ℂ) ⊗ₖ G)) (a, z) (b, z) =
      ∑ r, ∑ r', star (G r z) * S (a, r) (b, r') * G r' z := by
  simp only [Matrix.mul_apply, Matrix.kronecker_apply, Matrix.one_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_mul,
    mul_ite, mul_zero]
  rw [Finset.sum_eq_single b (fun x _ hx => by simp [hx]) (by simp)]
  simp only [if_true]
  have h : ∀ x : R, (∑ x_1 : X, ∑ x_2 : R, if a = x_1 then star (G x_2 z) * S (x_1, x_2) (b, x) * G x z else 0)
      = ∑ x_2 : R, star (G x_2 z) * S (a, x_2) (b, x) * G x z := by
    intro x
    rw [Finset.sum_comm]
    simp
  rw [Finset.sum_congr rfl (fun x _ => h x), Finset.sum_comm]

theorem solution {w c : ℕ} (G : Matrix (Reg w c) (Reg w c) ℂ) :
    (Matrix.of fun i j : QAlgorithms.Qubits w =>
      V G ((i, false), zeroReg w c) ((j, false), zeroReg w c)) =
    sandwich (purifVec G) := by
  ext i j
  simp only [Matrix.of_apply, V, sandwich, purifVec]
  exact gen_entry G (swapReg w c) (zeroReg w c) (i, false) (j, false)

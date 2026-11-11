-- Prove2me | solution 1 for PauliUnclonable531.Pauli.choi_identity
-- status  : ACCEPTED   (prove)
-- author  : @sragavan
-- created : 2026-11-10T10:44:04.646993+00:00
-- url     : https://prove2.me/submissions/3c9a1715-d8a0-4f98-9184-85e4330706de

import Mathlib
import Definitions.Def_PauliUnclonable531_Pauli_Choi

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false

namespace PauliUnclonable531.Pauli.ChoiAux

open PauliUnclonable531.Pauli

variable {A O : Type} [Fintype A] [DecidableEq A] [Fintype O]

lemma omega_block (a b : A) :
    (Matrix.of fun i i' => omegaDensity A (a, i) (b, i')) =
      (Fintype.card A : ℂ)⁻¹ • Matrix.single a b (1 : ℂ) := by
  ext i i'
  simp only [Matrix.of_apply, omegaDensity, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
  by_cases h1 : a = i <;> by_cases h2 : b = i' <;> simp [h1, h2, eq_comm]

lemma choi_apply (Φ : Op A →ₗ[ℂ] Op O) (a b : A) (x y : O) :
    choi Φ (a, x) (b, y) = (Fintype.card A : ℂ)⁻¹ * Φ (Matrix.single a b 1) x y := by
  unfold choi QAlgorithms.idTensorSuperop
  simp only [Matrix.of_apply]
  rw [omega_block, map_smul]
  rfl

lemma map_expand (Φ : Op A →ₗ[ℂ] Op O) (M : Op A) :
    Φ M = ∑ a, ∑ b, M a b • Φ (Matrix.single a b 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single M]
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← map_smul]
  congr 1
  ext i j
  simp [Matrix.single_apply]

lemma choi_eq (Φ : Op A →ₗ[ℂ] Op O) :
    choi Φ = ∑ a, ∑ b, (Fintype.card A : ℂ)⁻¹ •
      Matrix.kronecker (Matrix.single a b (1 : ℂ)) (Φ (Matrix.single a b 1)) := by
  ext ⟨a', x⟩ ⟨b', y⟩
  rw [choi_apply]
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.single_apply, smul_eq_mul]
  simp [ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']

lemma trace_transpose_single (M : Op A) (a b : A) :
    (M.transpose * Matrix.single a b 1).trace = M a b := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.single_apply, mul_ite, mul_one, mul_zero]
  simp only [ite_and, Finset.sum_ite_eq, Finset.mem_univ, if_true]

end PauliUnclonable531.Pauli.ChoiAux

open PauliUnclonable531.Pauli PauliUnclonable531.Pauli.ChoiAux in
theorem solution {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [Nonempty A] [Nonempty B] [Nonempty C]
    (Φ : Op A →ₗ[ℂ] Op (B × C)) (hΦ : WildeQIT.EntBreaking.IsQuantumChannel Φ)
    (M : Op A) (N : Op (B × C)) :
    (Fintype.card A : ℂ)⁻¹ * (N * Φ M).trace =
      (Matrix.kronecker M.transpose N * choi Φ).trace := by
  rw [choi_eq, Finset.mul_sum, Matrix.trace_sum]
  conv_lhs => rw [map_expand Φ M]
  simp only [Finset.mul_sum, Matrix.trace_sum, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [show Matrix.kronecker M.transpose N * Matrix.kronecker (Matrix.single a b (1 : ℂ))
      (Φ (Matrix.single a b 1)) = Matrix.kronecker (M.transpose * Matrix.single a b 1)
        (N * Φ (Matrix.single a b 1)) from (Matrix.mul_kronecker_mul _ _ _ _).symm]
  have htk : (Matrix.kronecker (M.transpose * Matrix.single a b 1)
      (N * Φ (Matrix.single a b 1))).trace =
      (M.transpose * Matrix.single a b 1).trace * (N * Φ (Matrix.single a b 1)).trace :=
    Matrix.trace_kronecker (M.transpose * Matrix.single a b 1) (N * Φ (Matrix.single a b 1))
  rw [htk, trace_transpose_single]

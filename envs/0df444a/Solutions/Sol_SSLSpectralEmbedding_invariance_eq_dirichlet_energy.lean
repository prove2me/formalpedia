-- Prove2me | solution 1 for SSLSpectralEmbedding.invariance_eq_dirichlet_energy
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T10:56:25.605873+00:00
-- url     : https://prove2.me/submissions/36fd970a-0950-4296-bc77-ddd046a1b90c

import Mathlib
import Definitions.Def_SSLSpectralEmbedding_Basic

set_option autoImplicit false

open Matrix
namespace SSLSpectralEmbedding

lemma de_vec {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) (hsym : ∀ i j, G j i = G i j)
    (z : Fin N → ℝ) :
    ∑ i, ∑ j, G i j * (z i - z j) ^ 2 =
      2 * ∑ j, (∑ i, z i * laplacian G i j) * z j := by
  have hL : ∀ j, (∑ i, z i * laplacian G i j) = z j * (∑ i, G j i) - ∑ i, z i * G i j := by
    intro j
    simp only [laplacian, degMat, Matrix.sub_apply, Matrix.diagonal_apply, mul_sub,
      Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [hL]
  have e1 : ∀ i j, G i j * (z i - z j) ^ 2 =
      G i j * z i ^ 2 + G i j * z j ^ 2 - 2 * (z i * G i j * z j) := by intros; ring
  simp only [e1, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have e2 : ∑ i, ∑ j, G i j * z j ^ 2 = ∑ i, ∑ j, G i j * z i ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
    rw [hsym]
  have e3 : ∑ j, (∑ i, z i * G i j) * z j = ∑ i, ∑ j, z i * G i j * z j := by
    simp only [Finset.sum_mul]; rw [Finset.sum_comm]
  have e4 : ∑ j, z j * (∑ i, G j i) * z j = ∑ i, ∑ j, G i j * z i ^ 2 := by
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum, Finset.sum_mul]; apply Finset.sum_congr rfl; intro j _; ring
  simp only [sub_mul, Finset.sum_sub_distrib]
  rw [e2, e3, e4]
  have e5 : ∑ i, ∑ j, 2 * (z i * G i j * z j) = 2 * ∑ i, ∑ j, z i * G i j * z j := by
    simp only [Finset.mul_sum]
  rw [e5]; ring

theorem invariance_eq_dirichlet_energy {N K : ℕ} (G : Matrix (Fin N) (Fin N) ℝ)
    (hG : IsRelationMatrix G) (Z : Matrix (Fin N) (Fin K) ℝ) :
    pairSum G Z = 2 * (Zᵀ * laplacian G * Z).trace := by
  have hsym : ∀ i j, G j i = G i j := fun i j => by
    have := hG.1; have h := congrFun (congrFun this i) j
    simpa [Matrix.transpose_apply] using h
  unfold pairSum
  have e : ∀ i j, G i j * ∑ k, (Z i k - Z j k) ^ 2 = ∑ k, G i j * (Z i k - Z j k) ^ 2 :=
    fun i j => Finset.mul_sum _ _ _
  simp only [e]
  have e' : ∑ i, ∑ j, ∑ k, G i j * (Z i k - Z j k) ^ 2 =
      ∑ k, ∑ i, ∑ j, G i j * (Z i k - Z j k) ^ 2 := by
    calc ∑ i, ∑ j, ∑ k, G i j * (Z i k - Z j k) ^ 2
        = ∑ i, ∑ k, ∑ j, G i j * (Z i k - Z j k) ^ 2 :=
          Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
      _ = ∑ k, ∑ i, ∑ j, G i j * (Z i k - Z j k) ^ 2 := Finset.sum_comm
  rw [e']
  have ht : (Zᵀ * laplacian G * Z).trace =
      ∑ k, ∑ j, (∑ i, Z i k * laplacian G i j) * Z j k := by
    simp [Matrix.trace, Matrix.mul_apply]
  rw [ht, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun k _ => de_vec G hsym (fun i => Z i k))

end SSLSpectralEmbedding

open SSLSpectralEmbedding in
theorem solution {N K : ℕ} (G : Matrix (Fin N) (Fin N) ℝ)
    (hG : IsRelationMatrix G) (Z : Matrix (Fin N) (Fin K) ℝ) :
    pairSum G Z = 2 * (Zᵀ * laplacian G * Z).trace :=
  SSLSpectralEmbedding.invariance_eq_dirichlet_energy G hG Z

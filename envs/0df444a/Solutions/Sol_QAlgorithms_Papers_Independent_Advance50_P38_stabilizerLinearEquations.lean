-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P38.stabilizerLinearEquations
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T09:27:09.617666+00:00
-- url     : https://prove2.me/submissions/1693ac9d-529f-44df-be13-f112fd384fab

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P38

namespace QAlgorithms.Papers.Independent.Advance50.P38

lemma cm_key {n : ℕ} (E K : Matrix (Fin n) (Fin n) ℂ) :
    (centralizerMatrix E).mulVec (colVec K) = fun ji => (E * K - K * E) ji.2 ji.1 := by
  funext ⟨j, i⟩
  unfold centralizerMatrix
  rw [Matrix.sub_mulVec]
  simp only [Matrix.mulVec, dotProduct, Matrix.kronecker_apply, colVec, Matrix.one_apply,
    Matrix.transpose_apply, Pi.sub_apply, Matrix.sub_apply, Matrix.mul_apply,
    Fintype.sum_prod_type]
  simp [Matrix.one_apply, mul_comm, ite_mul, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']



lemma comm_def {n : ℕ} (K E : Matrix (Fin n) (Fin n) ℂ) :
    QAlgorithms.Papers.Independent.Advance50.P38.comm K E = K * E - E * K := rfl

lemma cent_eq {n : ℕ} (E : Matrix (Fin n) (Fin n) ℂ) :
    centralizerAlgebra E = {K : (Matrix (Fin n) (Fin n) ℂ) | K.conjTranspose = -K ∧
      (centralizerMatrix E).mulVec (colVec K) = 0} := by
  ext K
  simp only [centralizerAlgebra, comm_def, Set.mem_setOf_eq, cm_key]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h; funext ji
    have h2 : E * K - K * E = 0 := by rw [← neg_sub, h, neg_zero]
    have := congrFun (congrFun h2 ji.2) ji.1
    simpa using this
  · intro h
    have h2 : E * K - K * E = 0 := by
      ext i j; simpa using congrFun h (j, i)
    rw [← neg_sub, h2, neg_zero]

lemma cent_lie {n : ℕ} (E K L : Matrix (Fin n) (Fin n) ℂ) (hK : K ∈ centralizerAlgebra E)
    (hL : L ∈ centralizerAlgebra E) :
    QAlgorithms.Papers.Independent.Advance50.P38.comm K L ∈ centralizerAlgebra E := by
  obtain ⟨hK, hKE⟩ := hK
  obtain ⟨hL, hLE⟩ := hL
  rw [comm_def] at hKE hLE
  refine ⟨?_, ?_⟩
  · rw [comm_def, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hK, hL]
    simp
  · have a : K * E = E * K := sub_eq_zero.mp hKE
    have b : L * E = E * L := sub_eq_zero.mp hLE
    rw [comm_def, comm_def, sub_eq_zero]
    calc (K * L - L * K) * E = K * (L * E) - L * (K * E) := by
          rw [Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_assoc]
      _ = K * (E * L) - L * (E * K) := by rw [a, b]
      _ = (K * E) * L - (L * E) * K := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
      _ = (E * K) * L - (E * L) * K := by rw [a, b]
      _ = E * (K * L - L * K) := by rw [Matrix.mul_sub, Matrix.mul_assoc, Matrix.mul_assoc]

lemma cent_shift {n : ℕ} (E : Matrix (Fin n) (Fin n) ℂ) (mu : ℂ) (Omega : Matrix (Fin n) (Fin n) ℂ)
    (hE : E = mu • (1 : Matrix (Fin n) (Fin n) ℂ) + Omega) :
    centralizerAlgebra E = centralizerAlgebra Omega := by
  ext K
  have : K * E - E * K = K * Omega - Omega * K := by
    subst hE
    rw [Matrix.mul_add, Matrix.add_mul]
    simp [Matrix.mul_smul, Matrix.smul_mul]
  simp only [centralizerAlgebra, comm_def, Set.mem_setOf_eq, this]

end QAlgorithms.Papers.Independent.Advance50.P38

open QAlgorithms.Papers.Independent.Advance50.P38 in
theorem solution {n : ℕ} (hn : 0 < n) (E : (Matrix (Fin n) (Fin n) ℂ)) :
    centralizerAlgebra E = {K : (Matrix (Fin n) (Fin n) ℂ) | K.conjTranspose = -K ∧
      (centralizerMatrix E).mulVec (colVec K) = 0} ∧
    (∀ K L : (Matrix (Fin n) (Fin n) ℂ), K ∈ centralizerAlgebra E → L ∈ centralizerAlgebra E →
      comm K L ∈ centralizerAlgebra E) ∧
    ∀ (mu : ℂ) (Omega : (Matrix (Fin n) (Fin n) ℂ)), Omega.conjTranspose = -Omega →
      E = mu • (1 : (Matrix (Fin n) (Fin n) ℂ)) + Omega → centralizerAlgebra E = centralizerAlgebra Omega :=
  ⟨cent_eq E, fun K L hK hL => cent_lie E K L hK hL,
    fun mu Omega _ hE => cent_shift E mu Omega hE⟩

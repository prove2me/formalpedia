-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P17.composition_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T05:15:44.975272+00:00
-- url     : https://prove2.me/submissions/748dd1cc-937e-4e6a-995f-5e6a494a5a33

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P17
noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix Kronecker Topology TensorProduct

open Filter

open QAlgorithms QAlgorithms.Papers.Independent.Support21.P17

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P50 (NoiseSpace completedTensorMap)

open QAlgorithms.Papers.Independent.Next46.P33 (UltraweakTest)

open QAlgorithms.Papers.Independent.Next46.P32 (PositiveKernel)

open QAlgorithms.Papers.Independent.Information100.P50 (M Lin coefficientMap)

lemma g66j_cpt (m n : ℕ)
    (A : M m) (B : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ) :
    (tracialV m n).conjTranspose * Matrix.kronecker A B * tracialV m n =
      (m : ℂ)⁻¹ • traceRight (Matrix.kronecker (1 : M n) A.transpose * B) := by
  ext ν ν'
  simp only [Matrix.mul_apply, tracialV, Matrix.conjTranspose_apply, Matrix.kronecker_apply,
    traceRight, Matrix.smul_apply, Matrix.of_apply, Matrix.transpose_apply, Fintype.sum_prod_type,
    Matrix.one_apply]
  simp only [apply_ite, star_zero, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero, one_mul]
  simp only [Matrix.kroneckerMap_apply, Matrix.kronecker, Matrix.one_apply, Matrix.transpose_apply,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hc : star (((Real.sqrt (m : ℝ))⁻¹ : ℝ) : ℂ) * (((Real.sqrt (m : ℝ))⁻¹ : ℝ) : ℂ) = (m : ℂ)⁻¹ := by
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← mul_inv,
      Real.mul_self_sqrt (Nat.cast_nonneg m)]
    push_cast; ring
  rw [smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  rw [Finset.sum_comm, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]
  rw [← hc]; ring

lemma g66j_lin_expand {m n : ℕ} (T : Lin m n) (A : M m) :
    T A = ∑ b, ∑ h, A b h • T (Matrix.single b h 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single A]
  simp only [map_sum]
  refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun h _ => ?_))
  rw [← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]

lemma g66j_recon (m n : ℕ) (hm : 0 < m) (T : Lin m n) (A : M m) :
    T A = (tracialV m n).conjTranspose * Matrix.kronecker A (scaledChoi T) * tracialV m n := by
  rw [g66j_cpt]
  ext ν ν'
  rw [g66j_lin_expand T A]
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  simp only [Matrix.sum_apply, Matrix.smul_apply, traceRight, Matrix.of_apply, Matrix.mul_apply,
    Fintype.sum_prod_type, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Matrix.transpose_apply, scaledChoi, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  field_simp

lemma g66j_choi_comp (m n d : ℕ) (hn : 0 < n) (T1 : Lin m n) (T2 : Lin n d) :
    scaledChoi (T2.comp T1) = bellCompression (scaledChoi T2) (scaledChoi T1) := by
  ext x y
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [scaledChoi, bellCompression, LinearMap.comp_apply]
  rw [g66j_lin_expand T2 (T1 _)]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun h _ => ?_))
  field_simp

theorem solution (m n d : ℕ) (hm : 0 < m) (hn : 0 < n) (hd : 0 < d)
    (T1 : Lin m n) (T2 : Lin n d)
    (hT1 : Entanglement.IsCompletelyPositive T1) (hT2 : Entanglement.IsCompletelyPositive T2) :
    scaledChoi (T2.comp T1) = bellCompression (scaledChoi T2) (scaledChoi T1) ∧
    (∀ A, T2 (T1 A) = (tracialV m d).conjTranspose *
      Matrix.kronecker A (bellCompression (scaledChoi T2) (scaledChoi T1)) * tracialV m d) ∧
    tracialDerivative (T2.comp T1) =
      Matrix.kronecker (1 : M m) (bellCompression (scaledChoi T2) (scaledChoi T1)) := by
  have hc := g66j_choi_comp m n d hn T1 T2
  refine ⟨hc, fun A => ?_, ?_⟩
  · rw [← hc]; exact g66j_recon m d hm (T2.comp T1) A
  · rw [tracialDerivative, hc]

end

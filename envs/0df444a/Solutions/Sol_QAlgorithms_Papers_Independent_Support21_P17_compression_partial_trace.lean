-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P17.compression_partial_trace
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T05:11:19.550988+00:00
-- url     : https://prove2.me/submissions/fc341685-92d7-418e-932b-8dc93d68b611

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

theorem solution (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
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

end

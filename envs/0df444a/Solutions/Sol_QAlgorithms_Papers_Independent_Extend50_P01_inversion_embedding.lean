-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P01.inversion_embedding
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-12T02:19:07.536671+00:00
-- url     : https://prove2.me/submissions/4f59a1dc-bee8-4b05-976e-b3fcd545543d

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P01

noncomputable section

open scoped Matrix Kronecker ComplexConjugate Matrix.Norms.L2Operator Manifold ContDiff

open MeasureTheory

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms QAlgorithms.Papers.Independent.Extend50.P01 in
theorem solution (x : Fin 3 → ℝ) :
    inversionEncoding (-x) = (1 ⊗ₖ pauliZ) * inversionEncoding x * (1 ⊗ₖ pauliZ) ∧
    (1 ⊗ₖ pauliZ : Matrix (Bool × Bool) (Bool × Bool) ℂ) ^ 2 = 1 := by
  have hZZ : (pauliZ : Matrix Bool Bool ℂ) * pauliZ = 1 := by
    ext i j
    cases i <;> cases j <;> simp [pauliZ, Matrix.mul_apply, Fintype.sum_bool, Matrix.diagonal_apply]
  have hZXZ : (pauliZ : Matrix Bool Bool ℂ) * pauliX * pauliZ = (-1 : ℂ) • pauliX := by
    ext i j
    cases i <;> cases j <;>
      simp [pauliZ, pauliX, Matrix.mul_apply, Fintype.sum_bool, Matrix.diagonal_apply]
  obtain ⟨U, hUdef⟩ : ∃ U : Matrix (Bool × Bool) (Bool × Bool) ℂ,
      U = (1 : Matrix Bool Bool ℂ) ⊗ₖ pauliZ := ⟨_, rfl⟩
  have hU : U * U = 1 := by
    rw [hUdef, ← Matrix.mul_kronecker_mul, Matrix.one_mul, hZZ, Matrix.one_kronecker_one]
  rw [← hUdef]
  refine ⟨?_, by rw [sq, hU]⟩
  have hUinv : U⁻¹ = U := Matrix.inv_eq_left_inv hU
  have hUunit : IsUnit U := ⟨⟨U, U, hU, hU⟩, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : Matrix (Bool × Bool) (Bool × Bool) ℂ,
      K = (∑ a, (x a : ℂ) • axis a) ⊗ₖ pauliX := ⟨_, rfl⟩
  have hconj : U * K * U = (-1 : ℂ) • K := by
    rw [hUdef, hK, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
      Matrix.mul_one, hZXZ, Matrix.kronecker_smul]
  have hM : (∑ a, (((-x) a : ℝ) : ℂ) • axis a) = (-1 : ℂ) • ∑ a, ((x a : ℝ) : ℂ) • axis a := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [smul_smul, Pi.neg_apply, Complex.ofReal_neg, neg_one_mul]
  unfold inversionEncoding QAlgorithms.Papers.Independent.Information100.P32.evolution
  rw [hM, Matrix.smul_kronecker, ← hK]
  have hR : U * NormedSpace.exp ((-(((1 / 2 : ℝ)) : ℂ) * Complex.I) • K) * U =
      U * NormedSpace.exp ((-(((1 / 2 : ℝ)) : ℂ) * Complex.I) • K) * U⁻¹ := by
    rw [hUinv]
  rw [hR, ← Matrix.exp_conj U _ hUunit, hUinv, Matrix.mul_smul, Matrix.smul_mul, hconj]

end

-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P16.triangularization_iffUnitary
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T18:26:59.459877+00:00
-- url     : https://prove2.me/submissions/a8f4d145-45d5-47bf-aa03-83d5f000f235

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P16

noncomputable section

open scoped BigOperators Matrix ComplexConjugate InnerProductSpace

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Dependency50.P16

lemma x8_qr {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) :
    ∃ U : Matrix (Fin n) (Fin n) ℂ, U ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
      (Uᴴ * B).IsUpperTriangular := by
  let b : Fin n → EuclideanSpace ℂ (Fin n) := fun j => WithLp.toLp 2 (fun k => B k j)
  have h : Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) = Fintype.card (Fin n) := by simp
  let ob := InnerProductSpace.gramSchmidtOrthonormalBasis h b
  refine ⟨(EuclideanSpace.basisFun (Fin n) ℂ).toBasis.toMatrix ob,
    OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary _ _, ?_⟩
  intro i j hij
  have := InnerProductSpace.gramSchmidtOrthonormalBasis_inv_triangular h b hij
  rw [← this, Matrix.mul_apply, PiLp.inner_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp [Module.Basis.toMatrix_apply, b, ob, mul_comm]

lemma x8_tri {n : ℕ} (A : Set (Matrix (Fin n) (Fin n) ℂ)) :
    triangularizable A ↔ unitarilyTriangularizable A := by
  constructor
  · rintro ⟨B, C, hBC, hCB, hX⟩
    obtain ⟨U, hU, hR⟩ := x8_qr B
    have hUU : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hU
    have hUU' : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hU
    set R := Uᴴ * B
    have hRS : R * (C * U) = 1 := by
      simp only [R, Matrix.mul_assoc]; rw [← Matrix.mul_assoc B, hBC, Matrix.one_mul, hUU]
    letI : Invertible R := invertibleOfRightInverse R (C * U) hRS
    have hinv : R⁻¹ = C * U := Matrix.inv_eq_right_inv hRS
    have hRi : (C * U).IsUpperTriangular := by
      rw [← hinv]; exact Matrix.blockTriangular_inv_of_blockTriangular hR
    refine ⟨U, hU, fun X hXA => ?_⟩
    have e : Uᴴ * X * U = R * (C * X * B) * (C * U) := by
      simp only [R, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc B C, hBC, Matrix.one_mul, ← Matrix.mul_assoc B C, hBC, Matrix.one_mul]
    rw [e]
    exact (hR.mul (hX X hXA)).mul hRi
  · rintro ⟨U, hU, hX⟩
    exact ⟨U, Uᴴ, Matrix.mem_unitaryGroup_iff.1 hU, Matrix.mem_unitaryGroup_iff'.1 hU, hX⟩

end QAlgorithms.Papers.Independent.Dependency50.P16


open scoped BigOperators Matrix ComplexConjugate ENNReal NNReal Matrix.Norms.L2Operator

open MeasureTheory Filter

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance 100] LieRing.ofAssociativeRing


local notation "Mat" => fun n : ℕ => Matrix (Fin n) (Fin n) ℂ

local notation "Vec" => fun n : ℕ => Fin n → ℝ

local notation "Hilbert" => fun n : ℕ => EuclideanSpace ℂ (Fin n)

local notation "Operator" => fun n : ℕ => Module.End ℂ (Mat n)

open QAlgorithms.Papers.Independent.Dependency50.P16 in
/-- arXiv:2308.00561v1, PDF p.12, Footnote 8: unitary triangularization.  -/
theorem solution {n : ℕ} (hn : 2 ≤ n) (A : Set (Mat n)) :
    triangularizable A ↔ unitarilyTriangularizable A :=
  x8_tri A




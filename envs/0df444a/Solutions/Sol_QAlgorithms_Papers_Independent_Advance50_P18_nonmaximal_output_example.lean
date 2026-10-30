-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P18.nonmaximal_output_example
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T13:02:03.366528+00:00
-- url     : https://prove2.me/submissions/7939dc0c-4c4e-4f0b-8d47-2b4e7222390f

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P18
namespace QAlgorithms.Papers.Independent.Advance50.P18

open scoped ComplexConjugate

noncomputable section

variable {K I A : Type*} [Fintype K] [DecidableEq K]
  [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A]

theorem s110c30_H_unitary : QAlgorithms.hadamard ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have hs : star QAlgorithms.hadamard = QAlgorithms.hadamard := by
    ext i j
    cases i <;> cases j <;> simp [QAlgorithms.hadamard, Matrix.star_apply, Complex.conj_ofReal]
  rw [hs]; exact QAlgorithms.hadamard_mul_self

theorem s110c30_s : ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹ = 1 / 2 := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; push_cast; ring

theorem s110c30_s2 : ((Real.sqrt 2 : ℂ))⁻¹ ^ 2 = 1 / 2 := by
  rw [sq, s110c30_s]

theorem s110c30_s4 : ((Real.sqrt 2 : ℂ))⁻¹ ^ 4 = 1 / 4 := by
  rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul, s110c30_s2]; norm_num

theorem s110c30_enc (psi : EuclideanSpace ℂ Bool)
    (hpsi : psi = QAlgorithms.ket false ∨ psi = QAlgorithms.act QAlgorithms.hadamard (QAlgorithms.ket false)) :
    encrypt exampleEnsemble (QAlgorithms.pureDensity psi) = hadamardExampleDensity := by
  rcases hpsi with rfl | rfl
  all_goals
    ext b c
    cases b <;> cases c <;>
      simp [encrypt, exampleEnsemble, hadamardExampleDensity, QAlgorithms.pureDensity,
        QAlgorithms.ket, QAlgorithms.act, QAlgorithms.hadamard, Matrix.mul_apply, Fintype.sum_bool,
        Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Complex.conj_ofReal] <;>
      ring_nf <;> simp only [s110c30_s2, s110c30_s4] <;> norm_num

open scoped ComplexOrder in
theorem s110c30_psd : hadamardExampleDensity.PosSemidef := by
  let B : Matrix (Fin 3) Bool ℂ :=
    Matrix.of fun i b => if b then (if i = 2 then 1/2 else 0) else 1/2
  have : hadamardExampleDensity = B.conjTranspose * B := by
    ext b c
    cases b <;> cases c <;>
      simp [B, hadamardExampleDensity, Matrix.mul_apply, Fin.sum_univ_three, map_ofNat] <;> norm_num
  rw [this]; exact Matrix.posSemidef_conjTranspose_mul_self B

theorem s110c30_state (psi : EuclideanSpace ℂ Bool)
    (hpsi : psi = QAlgorithms.ket false ∨ psi = QAlgorithms.act QAlgorithms.hadamard (QAlgorithms.ket false)) :
    QAlgorithms.IsState psi := by
  unfold QAlgorithms.IsState
  rcases hpsi with rfl | rfl
  · simp [QAlgorithms.ket]
  · rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one]
    simp [QAlgorithms.act, QAlgorithms.ket, QAlgorithms.hadamard, Matrix.mulVec, dotProduct,
      Fintype.sum_bool]

end

end QAlgorithms.Papers.Independent.Advance50.P18

open QAlgorithms QAlgorithms.Papers.Independent.Advance50.P18

theorem solution :
    BarePQC exampleSource exampleEnsemble hadamardExampleDensity ∧
      hadamardExampleDensity ≠ sourceMixedIdentity Bool := by
  refine ⟨⟨⟨fun _ => by simp [exampleEnsemble], by simp [exampleEnsemble, Fintype.sum_bool], ?_⟩,
    ⟨s110c30_psd, ?_⟩, fun psi hpsi => ⟨s110c30_state psi hpsi, s110c30_enc psi hpsi⟩⟩, ?_⟩
  · intro k; cases k
    · simp [exampleEnsemble]
    · simpa [exampleEnsemble] using s110c30_H_unitary
  · simp [Matrix.trace, hadamardExampleDensity, Fintype.sum_bool]; norm_num
  · intro h
    have := congrFun (congrFun h false) false
    simp [hadamardExampleDensity, sourceMixedIdentity] at this
    norm_num at this

-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier18.P05.gaussianDilation_covarianceForward
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:38:30.774678+00:00
-- url     : https://prove2.me/submissions/b9b40f4a-01f4-466a-9d70-6338567256ca

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P05

noncomputable section

open scoped ComplexOrder
open Matrix QAlgorithms.Papers.Independent.Dependency50.P10
  QAlgorithms.Papers.Independent.Frontier18.P05

namespace X5GaussianForward

lemma cx_mul {b c d : Type*} [Fintype c] (A : Matrix b c ℝ) (B : Matrix c d ℝ) :
    complexify (A * B) = complexify A * complexify B := by
  ext i j; simp [complexify, Matrix.mul_apply]

lemma cx_conjTranspose {b c : Type*} (A : Matrix b c ℝ) :
    (complexify A)ᴴ = complexify Aᵀ := by
  ext i j; simp [complexify, Matrix.conjTranspose_apply]

end X5GaussianForward

open X5GaussianForward in
theorem solution {n q : ℕ} (hn : 0 < n)
    (omega G : Matrix (Phase q) (Phase q) ℝ)
    (hOmega : IsEnvironmentalForm omega) (hG : physicalCovariance G omega)
    (s1 : Matrix (Phase n) (Phase n) ℝ)
    (s2 : Matrix (Phase n) (Phase q) ℝ)
    (s3 : Matrix (Phase q) (Phase n) ℝ)
    (s4 : Matrix (Phase q) (Phase q) ℝ)
    (hS : let S := Matrix.fromBlocks s1 s2 s3 s4
          let form := Matrix.fromBlocks (sigma n) 0 0 omega
          S * form * S.transpose = form) :
    ∃ X Y : Matrix (Phase n) (Phase n) ℝ,
      X = s1.transpose ∧ Y = s2 * G * s2.transpose ∧
      Y.transpose = Y ∧ Y.PosSemidef ∧ (cpMatrix X Y).PosSemidef ∧
      ∀ gamma : Matrix (Phase n) (Phase n) ℝ,
        physicalCovariance gamma (sigma n) →
        (let S := Matrix.fromBlocks s1 s2 s3 s4
         (S * Matrix.fromBlocks gamma 0 0 G * S.transpose).toBlocks₁₁ =
           X.transpose * gamma * X + Y) := by
  obtain ⟨hGt, hGpsd⟩ := hG
  have hTop : s1 * sigma n * s1ᵀ + s2 * omega * s2ᵀ = sigma n := by
    have := congrArg Matrix.toBlocks₁₁ hS
    simpa [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply] using this
  refine ⟨s1ᵀ, s2 * G * s2ᵀ, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · simp [Matrix.transpose_mul, hGt, Matrix.mul_assoc]
  · have hGr : G.PosSemidef := by
      refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
      · simpa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hGt
      · have h := hGpsd.dotProduct_mulVec_nonneg (fun i => (x i : ℂ))
        have hre := (Complex.nonneg_iff.1 h).1
        simpa [complexify, Matrix.sub_mulVec, Matrix.mulVec, dotProduct, Complex.mul_re,
          Finset.sum_sub_distrib, Matrix.smul_mulVec] using hre
    have := hGr.mul_mul_conjTranspose_same s2
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this
  · have hSig : commutatorDefect s1ᵀ = s2 * omega * s2ᵀ := by
      simp only [commutatorDefect, Matrix.transpose_transpose]
      rw [sub_eq_iff_eq_add]
      conv_lhs => rw [← hTop]
      exact add_comm _ _
    have hcp : cpMatrix s1ᵀ (s2 * G * s2ᵀ) = complexify s2 *
        (complexify G - Complex.I • complexify omega) * (complexify s2)ᴴ := by
      rw [cpMatrix, hSig, cx_conjTranspose, Matrix.mul_sub, Matrix.sub_mul, cx_mul, cx_mul, cx_mul,
        cx_mul, Matrix.mul_smul, Matrix.smul_mul]
    rw [hcp]
    exact hGpsd.mul_mul_conjTranspose_same _
  · intro gamma _
    simp [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.mul_assoc]

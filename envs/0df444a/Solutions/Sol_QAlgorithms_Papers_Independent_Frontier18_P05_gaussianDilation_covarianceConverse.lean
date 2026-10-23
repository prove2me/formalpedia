-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier18.P05.gaussianDilation_covarianceConverse
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T07:38:30.135727+00:00
-- url     : https://prove2.me/submissions/9b0f372c-635b-4d3a-85b1-7485ede95a4b

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P05
import Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P05_symplecticRows_completion

noncomputable section

open scoped ComplexOrder
open Matrix QAlgorithms.Papers.Independent.Dependency50.P10
  QAlgorithms.Papers.Independent.Frontier18.P05

namespace X5DilationConverse

lemma sigma_transpose (n : ℕ) : (sigma n)ᵀ = -sigma n := by
  simp [sigma, Matrix.fromBlocks_transpose, Matrix.fromBlocks_neg]

lemma sigma_mul_self (n : ℕ) : sigma n * sigma n = -1 := by
  simp [sigma, Matrix.fromBlocks_multiply, Matrix.fromBlocks_neg, ← Matrix.fromBlocks_one]

lemma cx_mul {a b c : Type*} [Fintype b] (A : Matrix a b ℝ) (B : Matrix b c ℝ) :
    complexify (A * B) = complexify A * complexify B := by
  ext i j; simp [complexify, Matrix.mul_apply]

/-- Every complex positive semidefinite matrix factors as `Z * Zᴴ`. -/
lemma exists_factor {a : Type*} [Fintype a] [DecidableEq a] (K : Matrix a a ℂ)
    (hK : K.PosSemidef) : ∃ Z : Matrix a a ℂ, Z * Zᴴ = K := by
  have hH := hK.isHermitian
  set U : Matrix a a ℂ := (hH.eigenvectorUnitary : Matrix a a ℂ)
  set lam := hH.eigenvalues
  have hlam : ∀ i, 0 ≤ lam i := fun i => hK.eigenvalues_nonneg i
  refine ⟨U * diagonal (fun i => ((Real.sqrt (lam i) : ℝ) : ℂ)), ?_⟩
  conv_rhs => rw [hH.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply, Matrix.conjTranspose_mul, Matrix.diagonal_conjTranspose,
    ← Matrix.star_eq_conjTranspose]
  have hd : diagonal (fun i => ((Real.sqrt (lam i) : ℝ) : ℂ)) *
      diagonal (star (fun i => ((Real.sqrt (lam i) : ℝ) : ℂ))) =
      diagonal (RCLike.ofReal ∘ lam) := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal, Function.comp_apply]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hlam i)]
    rfl
  calc U * diagonal (fun i => ((Real.sqrt (lam i) : ℝ) : ℂ)) *
        (diagonal (star (fun i => ((Real.sqrt (lam i) : ℝ) : ℂ))) * star U)
      = U * (diagonal (fun i => ((Real.sqrt (lam i) : ℝ) : ℂ)) *
        diagonal (star (fun i => ((Real.sqrt (lam i) : ℝ) : ℂ)))) * star U := by
        simp only [Matrix.mul_assoc]
    _ = U * diagonal (RCLike.ofReal ∘ lam) * star U := by rw [hd]

/-- The vacuum covariance is physical. -/
lemma physical_one (q : ℕ) : physicalCovariance (1 : Matrix (Phase q) (Phase q) ℝ) (sigma q) := by
  refine ⟨Matrix.transpose_one, ?_⟩
  set T : Matrix (Phase q) (Phase q) ℂ :=
    complexify (1 : Matrix (Phase q) (Phase q) ℝ) - Complex.I • complexify (sigma q)
  have h1 : complexify (1 : Matrix (Phase q) (Phase q) ℝ) = 1 := by
    ext i j; simp [complexify, Matrix.one_apply]; split_ifs <;> simp
  have hss : complexify (sigma q) * complexify (sigma q) = -1 := by
    rw [← cx_mul, sigma_mul_self]; ext i j; simp [complexify, Matrix.one_apply]
    split_ifs <;> simp
  have hst : (complexify (sigma q))ᴴ = -complexify (sigma q) := by
    ext i j
    have := congrFun (congrFun (sigma_transpose q) j) i
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at this
    simp [complexify, Matrix.conjTranspose_apply, this]
  have hTH : Tᴴ = T := by
    simp only [T, h1, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      Matrix.conjTranspose_smul, hst, Complex.star_def, Complex.conj_I, smul_neg, neg_smul,
      neg_neg]
  have e1 : (Complex.I • complexify (sigma q)) * (Complex.I • complexify (sigma q)) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hss, Complex.I_mul_I]; simp
  have hTT : Tᴴ * T = (2 : ℂ) • T := by
    rw [hTH]
    simp only [T, h1, sub_mul, mul_sub, one_mul, mul_one, e1]
    rw [two_smul]; abel
  have hT : T = (1 / 2 : ℝ) • (Tᴴ * T) := by
    rw [hTT]; ext i j; simp [Matrix.smul_apply]
  rw [hT]
  exact (Matrix.posSemidef_conjTranspose_mul_self T).smul (by norm_num)

end X5DilationConverse

open X5DilationConverse in
theorem solution {n : ℕ} (hn : 0 < n)
    (X Y : Matrix (Phase n) (Phase n) ℝ) (hCP : (cpMatrix X Y).PosSemidef) :
    ∃ q : ℕ, q ≤ 2 * n ∧
      ∃ G : Matrix (Phase q) (Phase q) ℝ,
        ∃ s2 : Matrix (Phase n) (Phase q) ℝ,
          ∃ s3 : Matrix (Phase q) (Phase n) ℝ,
            ∃ s4 : Matrix (Phase q) (Phase q) ℝ,
              physicalCovariance G (sigma q) ∧
              s2 * sigma q * s2.transpose = commutatorDefect X ∧
              s2 * G * s2.transpose = Y ∧
              (let S := Matrix.fromBlocks X.transpose s2 s3 s4
               S * jointSigma n q * S.transpose = jointSigma n q) ∧
              ∀ gamma : Matrix (Phase n) (Phase n) ℝ,
                physicalCovariance gamma (sigma n) →
                (let S := Matrix.fromBlocks X.transpose s2 s3 s4
                 (S * Matrix.fromBlocks gamma 0 0 G * S.transpose).toBlocks₁₁ =
                   X.transpose * gamma * X + Y) := by
  set Sig := commutatorDefect X with hSig
  obtain ⟨Z, hZ⟩ := exists_factor _ hCP
  -- real and imaginary parts of the factor
  let A : Matrix (Phase n) (Phase n) ℝ := Matrix.of fun i j => (Z i j).re
  let B : Matrix (Phase n) (Phase n) ℝ := Matrix.of fun i j => (Z i j).im
  have hentry : ∀ i j, (Z * Zᴴ) i j =
      ((∑ k, (A i k * A j k + B i k * B j k) : ℝ) : ℂ) +
        ((∑ k, (B i k * A j k - A i k * B j k) : ℝ) : ℂ) * Complex.I := by
    intro i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, A, B, Matrix.of_apply]
    push_cast
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  have hY : ∀ i j, Y i j = ∑ k, (A i k * A j k + B i k * B j k) := by
    intro i j
    have h := congrArg Complex.re (congrFun (congrFun hZ i) j)
    rw [hentry] at h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, zero_mul, add_zero] at h
    have hc : (cpMatrix X Y i j).re = Y i j := by simp [cpMatrix, complexify]
    rw [h, hc]
  have hS : ∀ i j, Sig i j = ∑ k, (A i k * B j k - B i k * A j k) := by
    intro i j
    have h := congrArg Complex.im (congrFun (congrFun hZ i) j)
    rw [hentry] at h
    simp only [Complex.add_im, Complex.ofReal_re, Complex.mul_im, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_mul, add_zero, zero_add] at h
    have hc : (cpMatrix X Y i j).im = -Sig i j := by simp [cpMatrix, complexify, Sig]
    rw [hc] at h
    rw [← neg_neg (Sig i j), ← h, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  -- the coupling block on `n + n` environment modes
  let eq : Fin (n + n) ≃ Phase n := finSumFinEquiv.symm
  let s2 : Matrix (Phase n) (Phase (n + n)) ℝ :=
    Matrix.of fun i x => Sum.elim (fun k => A i (eq k)) (fun k => B i (eq k)) x
  have hs2sig : s2 * sigma (n + n) * s2.transpose = Sig := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, sigma, Fintype.sum_sum_type,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.one_apply, Matrix.neg_apply, s2,
      Matrix.of_apply, Sum.elim_inl, Sum.elim_inr]
    simp only [mul_ite, mul_one, mul_zero, mul_neg, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, Finset.sum_neg_distrib, zero_add, add_zero, Finset.sum_const_zero, ite_mul,
      zero_mul, neg_mul, Finset.sum_ite_eq]
    rw [hS, ← eq.sum_comp (fun k => A i k * B j k - B i k * A j k), ← Finset.sum_neg_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hs2Y : s2 * (1 : Matrix (Phase (n + n)) (Phase (n + n)) ℝ) * s2.transpose = Y := by
    ext i j
    rw [hY, Matrix.mul_one, Matrix.mul_apply, Fintype.sum_sum_type]
    simp only [Matrix.transpose_apply, s2, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr]
    rw [← Finset.sum_add_distrib, ← eq.sum_comp (fun k => A i k * A j k + B i k * B j k)]
  -- complete the rows to a symplectic matrix
  have hRows : X.transpose * sigma n * X.transpose.transpose +
      s2 * sigma (n + n) * s2.transpose = sigma n := by
    rw [hs2sig, Matrix.transpose_transpose, hSig, commutatorDefect]
    abel
  obtain ⟨s3, s4, hsymp⟩ := symplecticRows_completion hn (sigma (n + n)) ⟨Equiv.refl _, rfl⟩
    X.transpose s2 hRows
  refine ⟨n + n, by omega, 1, s2, s3, s4, physical_one _, hs2sig, hs2Y, ?_, ?_⟩
  · exact hsymp
  · intro gamma _
    simp only [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₁,
      Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.transpose_transpose]
    rw [← hs2Y]

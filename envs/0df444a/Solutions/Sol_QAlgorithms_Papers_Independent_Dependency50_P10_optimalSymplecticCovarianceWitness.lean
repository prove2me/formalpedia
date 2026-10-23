-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P10.optimalSymplecticCovarianceWitness
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T07:43:37.487852+00:00
-- url     : https://prove2.me/submissions/664c0ddf-b111-4b91-9676-62f39dc43583

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P10
import Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P05_symplecticRows_completion

noncomputable section

open scoped ComplexOrder
open Matrix QAlgorithms.Papers.Independent.Dependency50.P10

namespace X5OptimalWitness

lemma sigma_transpose (n : ℕ) : (sigma n)ᵀ = -sigma n := by
  simp [sigma, Matrix.fromBlocks_transpose, Matrix.fromBlocks_neg]

lemma sigma_mul_self (n : ℕ) : sigma n * sigma n = -1 := by
  simp [sigma, Matrix.fromBlocks_multiply, Matrix.fromBlocks_neg, ← Matrix.fromBlocks_one]

lemma cx_mul {a b c : Type*} [Fintype b] (A : Matrix a b ℝ) (B : Matrix b c ℝ) :
    complexify (A * B) = complexify A * complexify B := by
  ext i j; simp [complexify, Matrix.mul_apply]

/-- Every complex positive semidefinite matrix factors as `Z * Zᴴ` with `rank` columns. -/
lemma exists_thin_factor {a : Type*} [Fintype a] [DecidableEq a] (K : Matrix a a ℂ)
    (hK : K.PosSemidef) : ∃ Z : Matrix a (Fin K.rank) ℂ, Z * Zᴴ = K := by
  have hH := hK.isHermitian
  set U : Matrix a a ℂ := (hH.eigenvectorUnitary : Matrix a a ℂ)
  set lam := hH.eigenvalues
  have hlam : ∀ i, 0 ≤ lam i := fun i => hK.eigenvalues_nonneg i
  have hcard : Fintype.card {i // lam i ≠ 0} = K.rank := (hH.rank_eq_card_non_zero_eigs).symm
  let e : Fin K.rank ≃ {i // lam i ≠ 0} := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨Matrix.of fun i k => U i (e k) * ((Real.sqrt (lam (e k)) : ℝ) : ℂ), ?_⟩
  have hK' : K = U * diagonal (RCLike.ofReal ∘ lam) * star U := by
    conv_lhs => rw [hH.spectral_theorem]
    rfl
  ext i j
  have hR : (U * diagonal (RCLike.ofReal ∘ lam) * star U : Matrix a a ℂ) i j =
      ∑ k, U i k * ((lam k : ℝ) : ℂ) * star (U j k) := by
    simp only [Matrix.mul_apply, Matrix.diagonal_apply, Function.comp_apply, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.star_apply]
    rfl
  have hKij : K i j = ∑ k, U i k * ((lam k : ℝ) : ℂ) * star (U j k) := by
    conv_lhs => rw [hK']
    exact hR
  have hterm : ∀ k : a, U i k * ((lam k : ℝ) : ℂ) * star (U j k) =
      U i k * ((Real.sqrt (lam k) : ℝ) : ℂ) * ((starRingEnd ℂ) (U j k) *
        ((Real.sqrt (lam k) : ℝ) : ℂ)) := by
    intro k
    have : ((lam k : ℝ) : ℂ) = ((Real.sqrt (lam k) : ℝ) : ℂ) * ((Real.sqrt (lam k) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hlam k)]
    rw [this, Complex.star_def]; ring
  rw [hKij, Finset.sum_congr rfl (fun k _ => hterm k), Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, Matrix.of_apply, star_mul', Complex.star_def,
    Complex.conj_ofReal]
  rw [e.sum_comp (fun k : {i // lam i ≠ 0} => U i k * ((Real.sqrt (lam k) : ℝ) : ℂ) *
      ((starRingEnd ℂ) (U j k) * ((Real.sqrt (lam k) : ℝ) : ℂ)))]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun k => lam k ≠ 0)]
  have h0 : ∑ k : {k // ¬ lam k ≠ 0}, U i k * ((Real.sqrt (lam k) : ℝ) : ℂ) *
      ((starRingEnd ℂ) (U j k) * ((Real.sqrt (lam k) : ℝ) : ℂ)) = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    have hk : lam k = 0 := not_not.mp k.2
    simp [hk]
  rw [h0, add_zero]

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

end X5OptimalWitness

open X5OptimalWitness in
theorem solution {n : ℕ}
    (X Y : Matrix (Phase n) (Phase n) ℝ)
    (hCP : (cpMatrix X Y).PosSemidef) :
    let q := (cpMatrix X Y).rank
    ∃ s2 : Matrix (Phase n) (Phase q) ℝ,
      ∃ G : Matrix (Phase q) (Phase q) ℝ,
        ∃ s3 : Matrix (Phase q) (Phase n) ℝ,
          ∃ s4 : Matrix (Phase q) (Phase q) ℝ,
            pureCovariance G (sigma q) ∧
            s2 * sigma q * s2.transpose = commutatorDefect X ∧
            s2 * G * s2.transpose = Y ∧
            (let S := Matrix.fromBlocks X.transpose s2 s3 s4
             S * jointSigma n q * S.transpose = jointSigma n q) := by
  intro q
  have hpure : pureCovariance (1 : Matrix (Phase q) (Phase q) ℝ) (sigma q) :=
    ⟨physical_one q, Matrix.det_one⟩
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨0, 1, 0, 1, hpure, Subsingleton.elim _ _, Subsingleton.elim _ _, ?_⟩
    simp only [jointSigma, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
      Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul,
      Matrix.transpose_zero, Matrix.transpose_one]
    congr 1
    exact Subsingleton.elim _ _
  set Sig := commutatorDefect X with hSig
  obtain ⟨Z, hZ⟩ := exists_thin_factor _ hCP
  let A : Matrix (Phase n) (Fin q) ℝ := Matrix.of fun i j => (Z i j).re
  let B : Matrix (Phase n) (Fin q) ℝ := Matrix.of fun i j => (Z i j).im
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
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero] at h
    have hc : (cpMatrix X Y i j).re = Y i j := by simp [cpMatrix, complexify]
    rw [h, hc]
  have hS : ∀ i j, Sig i j = ∑ k, (A i k * B j k - B i k * A j k) := by
    intro i j
    have h := congrArg Complex.im (congrFun (congrFun hZ i) j)
    rw [hentry] at h
    simp only [Complex.add_im, Complex.ofReal_re, Complex.mul_im, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_add] at h
    have hc : (cpMatrix X Y i j).im = -Sig i j := by simp [cpMatrix, complexify, Sig]
    rw [hc] at h
    rw [← neg_neg (Sig i j), ← h, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  let s2 : Matrix (Phase n) (Phase q) ℝ :=
    Matrix.of fun i x => Sum.elim (fun k => A i k) (fun k => B i k) x
  have hs2sig : s2 * sigma q * s2.transpose = Sig := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, sigma, Fintype.sum_sum_type,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.one_apply, Matrix.neg_apply, s2,
      Matrix.of_apply, Sum.elim_inl, Sum.elim_inr]
    simp only [mul_ite, mul_one, mul_zero, mul_neg, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, Finset.sum_neg_distrib, zero_add, add_zero, Finset.sum_const_zero, ite_mul,
      zero_mul, neg_mul, Finset.sum_ite_eq]
    rw [hS, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hs2Y : s2 * (1 : Matrix (Phase q) (Phase q) ℝ) * s2.transpose = Y := by
    ext i j
    rw [hY, Matrix.mul_one, Matrix.mul_apply, Fintype.sum_sum_type]
    simp only [Matrix.transpose_apply, s2, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr]
    rw [← Finset.sum_add_distrib]
  have hRows : X.transpose * sigma n * X.transpose.transpose +
      s2 * sigma q * s2.transpose = sigma n := by
    rw [hs2sig, Matrix.transpose_transpose, hSig, commutatorDefect]
    abel
  obtain ⟨s3, s4, hsymp⟩ :=
    QAlgorithms.Papers.Independent.Frontier18.P05.symplecticRows_completion hn (sigma q)
      ⟨Equiv.refl _, rfl⟩ X.transpose s2 hRows
  exact ⟨s2, 1, s3, s4, hpure, hs2sig, hs2Y, hsymp⟩

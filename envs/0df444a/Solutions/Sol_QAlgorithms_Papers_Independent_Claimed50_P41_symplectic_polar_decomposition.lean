-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P41.symplectic_polar_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:33:37.736457+00:00
-- url     : https://prove2.me/submissions/6539d2a4-695c-4683-9a88-d0585b05d6f0

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P41

open scoped MatrixOrder ComplexOrder

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

namespace X4Polar

open QAlgorithms.Papers.Independent.Claimed50.P41 Matrix

variable {n : ℕ}

abbrev Mat (n : ℕ) := Matrix (Phase n) (Phase n) ℝ

lemma sigma_transpose : (sigma n).transpose = -sigma n := by
  unfold sigma
  rw [Matrix.fromBlocks_transpose]
  simp [Matrix.fromBlocks_neg]

lemma sigma_mul_sigma : sigma n * sigma n = -1 := by
  unfold sigma
  rw [Matrix.fromBlocks_multiply]
  simp [Matrix.fromBlocks_neg, ← Matrix.fromBlocks_one]

lemma sigmaT_mul_sigma : (sigma n).transpose * sigma n = 1 := by
  rw [sigma_transpose, Matrix.neg_mul, sigma_mul_sigma, neg_neg]

lemma sigma_mul_sigmaT : sigma n * (sigma n).transpose = 1 := by
  rw [sigma_transpose, Matrix.mul_neg, sigma_mul_sigma, neg_neg]

lemma symp_mul {X Y : Mat n} (hX : PreservesCanonicalForm X) (hY : PreservesCanonicalForm Y) :
    PreservesCanonicalForm (X * Y) := by
  unfold PreservesCanonicalForm at *
  rw [Matrix.transpose_mul]
  calc X * Y * sigma n * (Y.transpose * X.transpose)
      = X * (Y * sigma n * Y.transpose) * X.transpose := by simp only [Matrix.mul_assoc]
    _ = sigma n := by rw [hY, hX]

lemma symp_isUnit {X : Mat n} (hX : PreservesCanonicalForm X) : IsUnit X.det := by
  have h := congrArg Matrix.det hX
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h
  have hs : IsUnit (sigma n).det := by
    have := congrArg Matrix.det (sigma_mul_sigmaT (n := n))
    rw [Matrix.det_mul, Matrix.det_one] at this
    exact isUnit_of_mul_isUnit_left (this ▸ isUnit_one)
  have : IsUnit (X.det * (sigma n).det * X.det) := by rw [h]; exact hs
  exact isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left this)

lemma symp_transpose {X : Mat n} (hX : PreservesCanonicalForm X) :
    PreservesCanonicalForm X.transpose := by
  unfold PreservesCanonicalForm at *
  rw [Matrix.transpose_transpose]
  have hu := symp_isUnit hX
  -- σ Xᵀ = X⁻¹ σ
  have h1 : sigma n * X.transpose = X⁻¹ * sigma n := by
    calc sigma n * X.transpose = X⁻¹ * (X * sigma n * X.transpose) := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
      _ = X⁻¹ * sigma n := by rw [hX]
  calc X.transpose * sigma n * X
      = (sigma n).transpose * (sigma n * X.transpose) * sigma n * X := by
        rw [← Matrix.mul_assoc, sigmaT_mul_sigma, Matrix.one_mul]
    _ = (sigma n).transpose * X⁻¹ * (sigma n * sigma n) * X := by
        rw [h1]; simp only [Matrix.mul_assoc]
    _ = sigma n := by
        rw [sigma_mul_sigma, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul,
          Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one, sigma_transpose, neg_neg]

lemma symp_inv {X : Mat n} (hX : PreservesCanonicalForm X) :
    PreservesCanonicalForm X⁻¹ := by
  unfold PreservesCanonicalForm at *
  have hu := symp_isUnit hX
  calc X⁻¹ * sigma n * X⁻¹.transpose = X⁻¹ * (X * sigma n * X.transpose) * X⁻¹.transpose := by
        rw [hX]
    _ = sigma n := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul,
          Matrix.mul_assoc, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hu,
          Matrix.transpose_one, Matrix.mul_one]

/-- The positive square root of a positive definite symplectic matrix is symplectic. -/
lemma sqrt_symp {M : Mat n} (hM : M.PosDef) (hMs : PreservesCanonicalForm M) :
    PreservesCanonicalForm (CFC.sqrt M) := by
  set P := CFC.sqrt M with hPdef
  have hP0 : P.PosSemidef := (CFC.sqrt_nonneg M).posSemidef
  have hPP : P * P = M := CFC.sqrt_mul_sqrt_self M hM.posSemidef.nonneg
  have hMu : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hM.isUnit
  have hPu : IsUnit P.det := by
    have := hMu; rw [← hPP, Matrix.det_mul] at this
    exact isUnit_of_mul_isUnit_left this
  have hMt : M.transpose = M := by
    have := hM.isHermitian
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hPt : P.transpose = P := by
    have := hP0.isHermitian
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  -- σᵀ M σ = M⁻¹
  have hMinv : (sigma n).transpose * M * sigma n = M⁻¹ := by
    unfold PreservesCanonicalForm at hMs
    rw [hMt] at hMs
    symm
    apply Matrix.inv_eq_left_inv
    calc (sigma n).transpose * M * sigma n * M = (sigma n).transpose * (M * sigma n * M) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hMs, sigmaT_mul_sigma]
  have hQ0 : ((sigma n).transpose * P * sigma n).PosSemidef := by
    have := hP0.conjTranspose_mul_mul_same (sigma n)
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this
  have hQQ : (sigma n).transpose * P * sigma n * ((sigma n).transpose * P * sigma n) = M⁻¹ := by
    rw [← hMinv, ← hPP]
    calc (sigma n).transpose * P * sigma n * ((sigma n).transpose * P * sigma n)
        = (sigma n).transpose * P * (sigma n * (sigma n).transpose) * P * sigma n := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [sigma_mul_sigmaT, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have hPi0 : P⁻¹.PosSemidef := hP0.inv
  have hPiPi : P⁻¹ * P⁻¹ = M⁻¹ := by
    rw [← hPP, Matrix.mul_inv_rev]
  have hQ : (sigma n).transpose * P * sigma n = P⁻¹ := by
    have h1 := (CFC.sqrt_eq_iff M⁻¹ _ hM.inv.posSemidef.nonneg hQ0.nonneg).mpr hQQ
    have h2 := (CFC.sqrt_eq_iff M⁻¹ _ hM.inv.posSemidef.nonneg hPi0.nonneg).mpr hPiPi
    rw [← h1, h2]
  unfold PreservesCanonicalForm
  rw [hPt]
  have hPs : P * sigma n = sigma n * P⁻¹ := by
    calc P * sigma n = sigma n * ((sigma n).transpose * P * sigma n) := by
          rw [← Matrix.mul_assoc (sigma n), ← Matrix.mul_assoc (sigma n),
            sigma_mul_sigmaT, Matrix.one_mul]
      _ = sigma n * P⁻¹ := by rw [hQ]
  rw [hPs, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hPu, Matrix.mul_one]

lemma transpose_of_posSemidef {M : Mat n} (h : M.PosSemidef) : M.transpose = M := by
  have := h.isHermitian
  rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this

lemma sqrt_facts {M : Mat n} (hM : M.PosDef) (hMs : PreservesCanonicalForm M) :
    IsPositiveSymplectic (CFC.sqrt M) ∧ CFC.sqrt M * CFC.sqrt M = M ∧
      IsUnit (CFC.sqrt M).det := by
  have hPP : CFC.sqrt M * CFC.sqrt M = M := CFC.sqrt_mul_sqrt_self M hM.posSemidef.nonneg
  have hMu : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hM.isUnit
  have hPu : IsUnit (CFC.sqrt M).det := by
    have := hMu; rw [← hPP, Matrix.det_mul] at this
    exact isUnit_of_mul_isUnit_left this
  refine ⟨⟨sqrt_symp hM hMs, ?_⟩, hPP, hPu⟩
  exact (CFC.sqrt_nonneg M).posSemidef.posDef_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr hPu)

lemma polar_KP (S : Mat n) (hS : PreservesCanonicalForm S) :
    ∃! factors : Mat n × Mat n,
      IsPassive factors.1 ∧ IsPositiveSymplectic factors.2 ∧ S = factors.1 * factors.2 := by
  have hSu := symp_isUnit hS
  set M := S.transpose * S with hMdef
  have hM : M.PosDef := by
    have := Matrix.PosDef.conjTranspose_mul_self S (fun x y hxy => by
      have := congrArg (fun z => S⁻¹ *ᵥ z) hxy
      simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hSu] using this)
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this
  have hMs : PreservesCanonicalForm M := symp_mul (symp_transpose hS) hS
  obtain ⟨⟨hPs, hPd⟩, hPP, hPu⟩ := sqrt_facts hM hMs
  set P := CFC.sqrt M with hPdef
  have hPt : P.transpose = P := transpose_of_posSemidef hPd.posSemidef
  refine ⟨(S * P⁻¹, P), ⟨⟨symp_mul hS (symp_inv hPs), ?_⟩, ⟨hPs, hPd⟩, ?_⟩, ?_⟩
  · rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hPt]
    calc P⁻¹ * S.transpose * (S * P⁻¹) = P⁻¹ * (P * P) * P⁻¹ := by
          rw [hPP, hMdef]; simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hPu, Matrix.one_mul,
            Matrix.mul_nonsing_inv _ hPu]
  · simp [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hPu]
  · rintro ⟨K', P'⟩ ⟨⟨-, hK'⟩, ⟨-, hP'⟩, hS'⟩
    have hP't : P'.transpose = P' := transpose_of_posSemidef hP'.posSemidef
    have hP'P' : P' * P' = M := by
      rw [hMdef, hS', Matrix.transpose_mul, hP't]
      calc P' * P' = P' * (K'.transpose * K') * P' := by rw [hK', Matrix.mul_one]
        _ = _ := by simp only [Matrix.mul_assoc]
    have hP'eq : P' = P := by
      rw [hPdef]
      exact ((CFC.sqrt_eq_iff M P' hM.posSemidef.nonneg hP'.posSemidef.nonneg).mpr hP'P').symm
    subst hP'eq
    refine Prod.ext ?_ rfl
    simp only
    rw [hS', Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hPu, Matrix.mul_one]

lemma polar_PK (S : Mat n) (hS : PreservesCanonicalForm S) :
    ∃! factors : Mat n × Mat n,
      IsPositiveSymplectic factors.1 ∧ IsPassive factors.2 ∧ S = factors.1 * factors.2 := by
  have hSu := symp_isUnit hS
  set N := S * S.transpose with hNdef
  have hN : N.PosDef := by
    have := Matrix.PosDef.mul_conjTranspose_self S (fun x y hxy => by
      have := congrArg (fun z => z ᵥ* S⁻¹) hxy
      simpa [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hSu] using this)
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this
  have hNs : PreservesCanonicalForm N := symp_mul hS (symp_transpose hS)
  obtain ⟨⟨hPs, hPd⟩, hPP, hPu⟩ := sqrt_facts hN hNs
  set P := CFC.sqrt N with hPdef
  have hPt : P.transpose = P := transpose_of_posSemidef hPd.posSemidef
  refine ⟨(P, P⁻¹ * S), ⟨⟨hPs, hPd⟩, ⟨symp_mul (symp_inv hPs) hS, ?_⟩, ?_⟩, ?_⟩
  · apply mul_eq_one_comm.mp
    rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hPt]
    calc P⁻¹ * S * (S.transpose * P⁻¹) = P⁻¹ * (P * P) * P⁻¹ := by
          rw [hPP, hNdef]; simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hPu, Matrix.one_mul,
            Matrix.mul_nonsing_inv _ hPu]
  · simp [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hPu]
  · rintro ⟨P', K'⟩ ⟨⟨-, hP'⟩, ⟨-, hK'⟩, hS'⟩
    have hK'' : K' * K'.transpose = 1 := mul_eq_one_comm.mp hK'
    have hP't : P'.transpose = P' := transpose_of_posSemidef hP'.posSemidef
    have hP'P' : P' * P' = N := by
      rw [hNdef, hS', Matrix.transpose_mul, hP't]
      calc P' * P' = P' * (K' * K'.transpose) * P' := by rw [hK'', Matrix.mul_one]
        _ = _ := by simp only [Matrix.mul_assoc]
    have hP'eq : P' = P := by
      rw [hPdef]
      exact ((CFC.sqrt_eq_iff N P' hN.posSemidef.nonneg hP'.posSemidef.nonneg).mpr hP'P').symm
    subst hP'eq
    refine Prod.ext rfl ?_
    simp only
    rw [hS', ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hPu, Matrix.one_mul]

end X4Polar

open X4Polar QAlgorithms.Papers.Independent.Claimed50.P41 in
theorem solution (n : ℕ) (hn : 0 < n)
    (S : Matrix (Phase n) (Phase n) ℝ) (hS : PreservesCanonicalForm S) :
    (∃! factors : Matrix (Phase n) (Phase n) ℝ × Matrix (Phase n) (Phase n) ℝ,
      IsPassive factors.1 ∧ IsPositiveSymplectic factors.2 ∧ S = factors.1 * factors.2) ∧
    (∃! factors : Matrix (Phase n) (Phase n) ℝ × Matrix (Phase n) (Phase n) ℝ,
      IsPositiveSymplectic factors.1 ∧ IsPassive factors.2 ∧ S = factors.1 * factors.2) :=
  ⟨polar_KP S hS, polar_PK S hS⟩

-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P41.pre_iwasawa_explicit_unique
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:41:57.001266+00:00
-- url     : https://prove2.me/submissions/227869ba-dfa8-4373-9d4b-625facaf4bbd

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P41

open scoped MatrixOrder ComplexOrder Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

namespace X4PreIwasawa

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


abbrev Sq (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

lemma complexify_mul (P Q : Sq n) : complexify (P * Q) = complexify P * complexify Q := by
  ext i j
  simp [complexify, Matrix.mul_apply]

lemma tr_of_psd {M : Sq n} (h : M.PosSemidef) : M.transpose = M := by
  have := h.isHermitian
  rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this

/-- Block relations of a symplectic matrix and of its transpose. -/
structure Rel (A B C D : Sq n) : Prop where
  s11 : A * B.transpose = B * A.transpose
  s12 : A * D.transpose = 1 + B * C.transpose
  t11 : A.transpose * C = C.transpose * A
  t12 : C.transpose * B = A.transpose * D - 1
  t21 : D.transpose * A = B.transpose * C + 1
  t22 : D.transpose * B = B.transpose * D

lemma rel_of {A B C D : Sq n} (hS : PreservesCanonicalForm (Matrix.fromBlocks A B C D)) :
    Rel A B C D := by
  have hT := symp_transpose hS
  unfold PreservesCanonicalForm sigma at hS hT
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_inj] at hS
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_transpose, Matrix.transpose_transpose,
    Matrix.transpose_transpose, Matrix.transpose_transpose, Matrix.transpose_transpose,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj] at hT
  obtain ⟨a1, a2, -, -⟩ := hS
  obtain ⟨b1, b2, b3, b4⟩ := hT
  simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg, zero_add, add_zero,
    Matrix.neg_mul] at a1 a2 b1 b2 b3 b4
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((neg_add_eq_zero).mp a1).symm
  · rw [← a2]; abel
  · exact ((neg_add_eq_zero).mp b1).symm
  · rw [← b2]; abel
  · calc D.transpose * A = -(-(D.transpose * A) + B.transpose * C) + B.transpose * C := by abel
      _ = _ := by rw [b3]; abel
  · exact ((neg_add_eq_zero).mp b4)


lemma inv_tr {M : Sq n} (h : M.transpose = M) : (M⁻¹).transpose = M⁻¹ := by
  rw [Matrix.transpose_nonsing_inv, h]

/-- Basic data: `G = AAᵀ + BBᵀ`, `H' = CAᵀ + DBᵀ`. -/
lemma G_facts {A B C D : Sq n} (hS : PreservesCanonicalForm (Matrix.fromBlocks A B C D)) :
    (A * A.transpose + B * B.transpose).PosDef ∧
    (A * A.transpose + B * B.transpose) * (C * A.transpose + D * B.transpose) =
      (A * C.transpose + B * D.transpose) * (A * A.transpose + B * B.transpose) := by
  have hSu := symp_isUnit hS
  set S := Matrix.fromBlocks A B C D with hSdef
  have hSS : (S * S.transpose).PosDef := by
    have := Matrix.PosDef.mul_conjTranspose_self S (fun x y hxy => by
      have := congrArg (fun z => z ᵥ* S⁻¹) hxy
      simpa [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hSu] using this)
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this
  have hblk : S * S.transpose = Matrix.fromBlocks (A * A.transpose + B * B.transpose)
      (A * C.transpose + B * D.transpose) (C * A.transpose + D * B.transpose)
      (C * C.transpose + D * D.transpose) := by
    rw [hSdef, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
  have hSSs : PreservesCanonicalForm (S * S.transpose) := symp_mul hS (symp_transpose hS)
  rw [hblk] at hSS hSSs
  refine ⟨?_, ?_⟩
  · have := hSS.submatrix (e := Sum.inl) Sum.inl_injective
    exact this
  · have r := (rel_of hSSs).s11
    have hGt : (A * A.transpose + B * B.transpose).transpose = A * A.transpose + B * B.transpose := by
      simp [Matrix.transpose_add, Matrix.transpose_mul]
    rw [hGt] at r
    rw [← r]
    congr 1
    simp [Matrix.transpose_add, Matrix.transpose_mul]

lemma passive_of (X Y : Sq n) (hXX : X * X.transpose + Y * Y.transpose = 1)
    (hXY : X * Y.transpose = Y * X.transpose) : IsPassive (passiveMatrix X Y) := by
  have hKt : (passiveMatrix X Y).transpose =
      Matrix.fromBlocks X.transpose (-Y.transpose) Y.transpose X.transpose := by
    unfold passiveMatrix; rw [Matrix.fromBlocks_transpose, Matrix.transpose_neg]
  have hKKt : passiveMatrix X Y * (passiveMatrix X Y).transpose = 1 := by
    rw [hKt]; unfold passiveMatrix
    rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
    refine Matrix.fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩ <;>
      (try simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg]) <;>
      first
      | exact hXX
      | (rw [add_comm]; exact hXX)
      | (rw [hXY]; abel)
  refine ⟨?_, mul_eq_one_comm.mp hKKt⟩
  unfold PreservesCanonicalForm
  rw [hKt]; unfold passiveMatrix sigma
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  refine Matrix.fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg, zero_add, add_zero,
      Matrix.neg_mul, neg_neg] <;>
    first
    | exact hXX
    | (rw [add_comm]; exact hXX)
    | (rw [← neg_add, hXX])
    | (rw [← neg_add, add_comm, hXX])
    | (rw [hXY]; abel)

end X4PreIwasawa

open X4PreIwasawa QAlgorithms.Papers.Independent.Claimed50.P41 in
theorem solution (n : ℕ) (hn : 0 < n)
    (A B C D : Matrix (Fin n) (Fin n) ℝ)
    (hS : PreservesCanonicalForm (Matrix.fromBlocks A B C D)) :
    let R := preA A B
    let Czero := preC A B C D
    let X := R⁻¹ * A
    let Y := R⁻¹ * B
    (A * A.transpose + B * B.transpose).PosDef ∧ R.PosDef ∧
    R * R = A * A.transpose + B * B.transpose ∧ IsUnit R.det ∧
    (Czero * R⁻¹).IsSymm ∧ IsPassive (passiveMatrix X Y) ∧
    unitaryParameter X Y = complexify R⁻¹ * unitaryParameter A B ∧
    Matrix.fromBlocks A B C D = lensMatrix (Czero * R⁻¹) * glMatrix R * passiveMatrix X Y ∧
    (∃! f : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ ×
      Matrix (Phase n) (Phase n) ℝ,
      f.1.IsSymm ∧ f.2.1.PosDef ∧ IsPassive f.2.2 ∧
        Matrix.fromBlocks A B C D = lensMatrix f.1 * glMatrix f.2.1 * f.2.2) := by
  intro R Czero X Y
  have rel := rel_of hS
  obtain ⟨hG, hGH⟩ := G_facts hS
  set G := A * A.transpose + B * B.transpose with hGdef
  set H' := C * A.transpose + D * B.transpose with hH'def
  set H := A * C.transpose + B * D.transpose with hHdef
  have hGt : G.transpose = G := tr_of_psd hG.posSemidef
  have hGu : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).mp hG.isUnit
  -- the square root
  have hRR : R * R = G := by
    show cfc Real.sqrt G * cfc Real.sqrt G = G
    have hsa : IsSelfAdjoint G := hG.isHermitian
    rw [← cfc_mul (fun x => Real.sqrt x) (fun x => Real.sqrt x) G]
    conv_rhs => rw [← cfc_id' ℝ G]
    apply cfc_congr
    intro x hx
    have : 0 < x := by
      rw [hG.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
      obtain ⟨i, rfl⟩ := hx
      exact hG.eigenvalues_pos i
    simp [Real.mul_self_sqrt this.le]
  have hR0' : 0 ≤ R := cfc_nonneg (fun x _ => Real.sqrt_nonneg x)
  have hR0 : R.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hR0'
  have hRdef : R = CFC.sqrt G :=
    ((CFC.sqrt_eq_iff G R (Matrix.nonneg_iff_posSemidef.mpr hG.posSemidef) hR0').mpr hRR).symm
  have hRu : IsUnit R.det := by
    have := hGu; rw [← hRR, Matrix.det_mul] at this
    exact isUnit_of_mul_isUnit_left this
  have hRpd : R.PosDef := hR0.posDef_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr hRu)
  have hRt : R.transpose = R := tr_of_psd hR0
  have hRit : (R⁻¹).transpose = R⁻¹ := inv_tr hRt
  have hRRi : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv _ hRu
  have hRiR : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul _ hRu
  have hGGi : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv _ hGu
  have hGiG : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul _ hGu
  have hRiRi : R⁻¹ * R⁻¹ = G⁻¹ := by rw [← hRR, Matrix.mul_inv_rev]
  -- the lens parameter
  have hL : Czero * R⁻¹ = H' * G⁻¹ := by
    show (C * A.transpose + D * B.transpose) * (preA A B)⁻¹ * R⁻¹ = _
    rw [Matrix.mul_assoc]; exact congrArg (H' * ·) hRiRi
  have hH't : H'.transpose = H := by simp [hH'def, hHdef, Matrix.transpose_add, Matrix.transpose_mul]
  have hLsym : H' * G⁻¹ = G⁻¹ * H := by
    calc H' * G⁻¹ = G⁻¹ * (G * H') * G⁻¹ := by
          rw [← Matrix.mul_assoc, hGiG, Matrix.one_mul]
      _ = G⁻¹ * H := by rw [hGH, Matrix.mul_assoc, Matrix.mul_assoc, hGGi, Matrix.mul_one]
  have hLt : (H' * G⁻¹).IsSymm := by
    unfold Matrix.IsSymm
    rw [Matrix.transpose_mul, inv_tr hGt, hH't, hLsym]
  -- X, Y identities
  have hXX : X * X.transpose + Y * Y.transpose = 1 := by
    show R⁻¹ * A * (R⁻¹ * A).transpose + R⁻¹ * B * (R⁻¹ * B).transpose = 1
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hRit]
    calc R⁻¹ * A * (A.transpose * R⁻¹) + R⁻¹ * B * (B.transpose * R⁻¹) = R⁻¹ * G * R⁻¹ := by
          simp only [hGdef, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = 1 := by rw [← hRR, ← Matrix.mul_assoc, hRiR, Matrix.one_mul, hRRi]
  have hXY : X * Y.transpose = Y * X.transpose := by
    show R⁻¹ * A * (R⁻¹ * B).transpose = R⁻¹ * B * (R⁻¹ * A).transpose
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hRit]
    calc R⁻¹ * A * (B.transpose * R⁻¹) = R⁻¹ * (A * B.transpose) * R⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [rel.s11]; simp only [Matrix.mul_assoc]
  have hK : IsPassive (passiveMatrix X Y) := passive_of X Y hXX hXY
  have hUP : unitaryParameter X Y = complexify R⁻¹ * unitaryParameter A B := by
    show complexify (R⁻¹ * A) - Complex.I • complexify (R⁻¹ * B) =
      complexify R⁻¹ * (complexify A - Complex.I • complexify B)
    rw [complexify_mul, complexify_mul, Matrix.mul_sub, Matrix.mul_smul]
  have hHA : H * A - B = G * C := by
    have e1 : C.transpose * A = A.transpose * C := rel.t11.symm
    calc H * A - B = A * (C.transpose * A) + B * (D.transpose * A) - B := by
          simp only [hHdef, Matrix.add_mul, Matrix.mul_assoc]
      _ = G * C := by
          rw [e1, rel.t21, hGdef, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul]
          simp only [Matrix.mul_assoc]; abel
  have hHB : H * B + A = G * D := by
    calc H * B + A = A * (C.transpose * B) + B * (D.transpose * B) + A := by
          simp only [hHdef, Matrix.add_mul, Matrix.mul_assoc]
      _ = G * D := by
          rw [rel.t12, rel.t22, hGdef, Matrix.mul_sub, Matrix.mul_one, Matrix.add_mul]
          simp only [Matrix.mul_assoc]; abel
  have hfac : Matrix.fromBlocks A B C D =
      lensMatrix (H' * G⁻¹) * glMatrix R * passiveMatrix X Y := by
    unfold lensMatrix glMatrix passiveMatrix
    rw [hRit, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
      Matrix.mul_neg, neg_zero]
    refine Matrix.fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩
    · show A = R * (R⁻¹ * A); rw [← Matrix.mul_assoc, hRRi, Matrix.one_mul]
    · show B = R * (R⁻¹ * B); rw [← Matrix.mul_assoc, hRRi, Matrix.one_mul]
    · show C = H' * G⁻¹ * R * (R⁻¹ * A) + -(R⁻¹ * (R⁻¹ * B))
      rw [Matrix.mul_assoc (H' * G⁻¹) R, ← Matrix.mul_assoc R, hRRi, Matrix.one_mul,
        ← Matrix.mul_assoc R⁻¹ R⁻¹, hRiRi, hLsym, Matrix.mul_assoc, ← Matrix.mul_neg,
        ← Matrix.mul_add, ← sub_eq_add_neg, hHA, ← Matrix.mul_assoc, hGiG, Matrix.one_mul]
    · show D = H' * G⁻¹ * R * (R⁻¹ * B) + R⁻¹ * (R⁻¹ * A)
      rw [Matrix.mul_assoc (H' * G⁻¹) R, ← Matrix.mul_assoc R, hRRi, Matrix.one_mul,
        ← Matrix.mul_assoc R⁻¹ R⁻¹, hRiRi, hLsym, Matrix.mul_assoc, ← Matrix.mul_add, hHB,
        ← Matrix.mul_assoc, hGiG, Matrix.one_mul]
  refine ⟨hG, hRpd, hRR, hRu, by rw [hL]; exact hLt, hK, hUP, by rw [hL]; exact hfac, ?_⟩
  refine ⟨(H' * G⁻¹, R, passiveMatrix X Y), ⟨hLt, hRpd, hK, hfac⟩, ?_⟩
  rintro ⟨L', R', K'⟩ ⟨hL', hR', hK', hS'⟩
  simp only at hL' hR' hK' hS'
  have hR'0 := hR'.posSemidef
  have hR't : R'.transpose = R' := tr_of_psd hR'0
  have hR'u : IsUnit R'.det := (Matrix.isUnit_iff_isUnit_det _).mp hR'.isUnit
  have hR'it := inv_tr hR't
  have hK'' : K' * K'.transpose = 1 := mul_eq_one_comm.mp hK'.2
  have hlhs : Matrix.fromBlocks A B C D * (Matrix.fromBlocks A B C D).transpose =
      Matrix.fromBlocks G H H' (C * C.transpose + D * D.transpose) := by
    rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
  have hrhs : Matrix.fromBlocks A B C D * (Matrix.fromBlocks A B C D).transpose =
      lensMatrix L' * glMatrix R' * (glMatrix R').transpose * (lensMatrix L').transpose := by
    rw [hS', Matrix.transpose_mul, Matrix.transpose_mul]
    calc lensMatrix L' * glMatrix R' * K' * (K'.transpose * ((glMatrix R').transpose *
          (lensMatrix L').transpose))
        = lensMatrix L' * glMatrix R' * (K' * K'.transpose) * (glMatrix R').transpose *
          (lensMatrix L').transpose := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hK'', Matrix.mul_one]
  rw [hlhs] at hrhs
  unfold lensMatrix glMatrix at hrhs
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_transpose, hR'it, hR't,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply] at hrhs
  simp only [Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
    Matrix.mul_one, Matrix.transpose_zero, Matrix.transpose_one] at hrhs
  obtain ⟨e1, -, e3, -⟩ := Matrix.fromBlocks_inj.mp hrhs
  have hR'eq : R' = R := by
    rw [hRdef]
    exact ((CFC.sqrt_eq_iff G R' (Matrix.nonneg_iff_posSemidef.mpr hG.posSemidef)
      (Matrix.nonneg_iff_posSemidef.mpr hR'0)).mpr e1.symm).symm
  have hL'eq : L' = H' * G⁻¹ := by
    calc L' = L' * (R' * R') * G⁻¹ := by
          rw [← e1, Matrix.mul_assoc, hGGi, Matrix.mul_one]
      _ = H' * G⁻¹ := by rw [e3]; simp only [Matrix.mul_assoc]
  rw [hR'eq, hL'eq] at hS'
  set M := lensMatrix (H' * G⁻¹) * glMatrix R with hMdef
  have hMu : IsUnit M.det := by
    rw [hMdef, Matrix.det_mul]
    unfold lensMatrix glMatrix
    rw [Matrix.det_fromBlocks_zero₁₂, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, one_mul,
      Matrix.det_transpose]
    simp only [one_mul]
    exact (hRu.mul (Matrix.isUnit_nonsing_inv_det R hRu))
  have hK'eq : K' = passiveMatrix X Y := by
    calc K' = M⁻¹ * (M * K') := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hMu, Matrix.one_mul]
      _ = M⁻¹ * (M * passiveMatrix X Y) := by
          rw [← hS', hfac]
      _ = _ := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hMu, Matrix.one_mul]
  rw [hL'eq, hR'eq, hK'eq]

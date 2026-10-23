-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P41.special_variance_families
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T07:19:13.865582+00:00
-- url     : https://prove2.me/submissions/33972568-aeee-4162-9316-6959733009dc

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P41

open scoped MatrixOrder ComplexOrder

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

namespace X4SF

open Matrix QAlgorithms.Papers.Independent.Claimed50.P41

section Polar
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

end Polar

section Ray
variable {m : Type*} [Fintype m] [DecidableEq m]

lemma quad_eq (A : Matrix m m ℝ) (hA : A.IsHermitian) (x : m → ℝ) :
    x ⬝ᵥ (A *ᵥ x) = ∑ i, hA.eigenvalues i * ((star (hA.eigenvectorUnitary).1) *ᵥ x) i ^ 2 := by
  have hspec := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hspec
  set U : Matrix m m ℝ := (hA.eigenvectorUnitary).1
  have hU : U * star U = 1 := Unitary.coe_mul_star_self _
  have hU' : star U * U = 1 := Unitary.coe_star_mul_self _
  set y := star U *ᵥ x
  have hx : x = U *ᵥ y := by simp [y, mulVec_mulVec, hU]
  have hs : star U = Uᵀ := rfl
  conv_lhs => rw [hspec]
  have h1 : star U *ᵥ (U *ᵥ y) = y := by rw [mulVec_mulVec, hU', one_mulVec]
  rw [hx, ← mulVec_mulVec, ← mulVec_mulVec, h1, dotProduct_mulVec]
  have : (U *ᵥ y) ᵥ* U = y := by
    rw [← mulVec_transpose, ← hs, mulVec_mulVec, hU', one_mulVec]
  rw [this, dotProduct, ]
  simp [mulVec_diagonal, sq]
  refine Finset.sum_congr rfl fun i _ => by ring

lemma norm_eq (A : Matrix m m ℝ) (hA : A.IsHermitian) (x : m → ℝ) :
    x ⬝ᵥ x = ∑ i, ((star (hA.eigenvectorUnitary).1) *ᵥ x) i ^ 2 := by
  set U : Matrix m m ℝ := (hA.eigenvectorUnitary).1
  have hU : U * star U = 1 := Unitary.coe_mul_star_self _
  have hs : star U = Uᵀ := rfl
  have : (star U *ᵥ x) ⬝ᵥ (star U *ᵥ x) = x ⬝ᵥ x := by
    rw [dotProduct_mulVec, hs, vecMul_transpose, mulVec_mulVec, ← hs, hU, one_mulVec]
  rw [← this, dotProduct]
  simp [sq]

lemma inf_mul_le (A : Matrix m m ℝ) (hA : A.IsHermitian) (hne : (Finset.univ : Finset m).Nonempty)
    (x : m → ℝ) : Finset.univ.inf' hne hA.eigenvalues * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x) := by
  rw [quad_eq A hA, norm_eq A hA x, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_right (Finset.inf'_le _ (Finset.mem_univ i)) (sq_nonneg _)

lemma exists_attain (A : Matrix m m ℝ) (hA : A.IsHermitian) (hne : (Finset.univ : Finset m).Nonempty) :
    ∃ x : m → ℝ, x ⬝ᵥ x = 1 ∧ x ⬝ᵥ (A *ᵥ x) = Finset.univ.inf' hne hA.eigenvalues := by
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_inf' hne hA.eigenvalues
  refine ⟨hA.eigenvectorBasis j, ?_, ?_⟩
  · have := hA.eigenvectorBasis.orthonormal.1 j
    rw [EuclideanSpace.norm_eq] at this
    have h2 : ∑ i, ‖(hA.eigenvectorBasis j) i‖ ^ 2 = 1 := by
      have := congrArg (· ^ 2) this
      simp only [one_pow] at this
      rwa [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at this
    rw [dotProduct]
    simpa [sq] using h2
  · rw [hj]
    have := hA.eigenvalues_eq j
    simp only [RCLike.re_to_real, star_trivial] at this
    rw [this, dotProduct_comm]

lemma inf_congr (hne : (Finset.univ : Finset m).Nonempty) {A B : Matrix m m ℝ} (h : A = B)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    Finset.univ.inf' hne hA.eigenvalues = Finset.univ.inf' hne hB.eigenvalues := by
  subst h; rfl

/-- Conjugation by an orthogonal matrix does not decrease the minimal eigenvalue. -/
lemma inf_le_conj (A : Matrix m m ℝ) (hA : A.IsHermitian) (hne : (Finset.univ : Finset m).Nonempty)
    (Q : Matrix m m ℝ) (hQ : Q * Qᵀ = 1) (hB : (Q * A * Qᵀ).IsHermitian) :
    Finset.univ.inf' hne hA.eigenvalues ≤ Finset.univ.inf' hne hB.eigenvalues := by
  obtain ⟨x, hx1, hx⟩ := exists_attain _ hB hne
  rw [← hx]
  have h := inf_mul_le A hA hne (Qᵀ *ᵥ x)
  have e1 : (Qᵀ *ᵥ x) ⬝ᵥ (Qᵀ *ᵥ x) = x ⬝ᵥ x := by
    rw [dotProduct_mulVec, vecMul_transpose, mulVec_mulVec, hQ, one_mulVec]
  have e2 : (Qᵀ *ᵥ x) ⬝ᵥ (A *ᵥ (Qᵀ *ᵥ x)) = x ⬝ᵥ ((Q * A * Qᵀ) *ᵥ x) := by
    symm
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose]
  rw [e1, e2, hx1, mul_one] at h
  exact h

lemma inf_conj_eq (A : Matrix m m ℝ) (hA : A.IsHermitian) (hne : (Finset.univ : Finset m).Nonempty)
    (Q : Matrix m m ℝ) (hQ : Qᵀ * Q = 1) (hB : (Q * A * Qᵀ).IsHermitian) :
    Finset.univ.inf' hne hB.eigenvalues = Finset.univ.inf' hne hA.eigenvalues := by
  have hQ' : Q * Qᵀ = 1 := mul_eq_one_comm.mp hQ
  refine le_antisymm ?_ (inf_le_conj A hA hne Q hQ' hB)
  have hA' : (Qᵀ * (Q * A * Qᵀ) * Qᵀᵀ) = A := by
    rw [transpose_transpose]
    simp only [← Matrix.mul_assoc, hQ, Matrix.one_mul]
    rw [Matrix.mul_assoc, hQ, Matrix.mul_one]
  have hC : (Qᵀ * (Q * A * Qᵀ) * Qᵀᵀ).IsHermitian := by rw [hA']; exact hA
  have := inf_le_conj (Q * A * Qᵀ) hB hne Qᵀ (by rw [transpose_transpose, hQ]) hC
  exact this.trans (le_of_eq (inf_congr hne hA' hC hA))


lemma inf_le_diag (A : Matrix m m ℝ) (hA : A.IsHermitian) (hne : (Finset.univ : Finset m).Nonempty)
    (a : m) : Finset.univ.inf' hne hA.eigenvalues ≤ A a a := by
  have := inf_mul_le A hA hne (Pi.single a 1)
  simpa using this

end Ray


lemma passive_of {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℝ) (h1 : X * Xᵀ + Y * Yᵀ = 1)
    (h2 : X * Yᵀ = Y * Xᵀ) : IsPassive (passiveMatrix X Y) := by
  have hKKt : passiveMatrix X Y * (passiveMatrix X Y)ᵀ = 1 := by
    unfold passiveMatrix
    rw [fromBlocks_transpose, fromBlocks_multiply, ← fromBlocks_one]
    simp only [transpose_neg, Matrix.mul_neg, Matrix.neg_mul, neg_neg]
    congr 1
    · rw [h2]; abel
    · rw [h2]; abel
    · rw [add_comm]; exact h1
  refine ⟨?_, mul_eq_one_comm.mp hKKt⟩
  unfold PreservesCanonicalForm passiveMatrix sigma
  rw [fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
  simp only [transpose_neg, Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_zero, Matrix.zero_mul,
    Matrix.mul_one, zero_add, add_zero, neg_zero]
  congr 1
  · rw [h2]; abel
  · rw [add_comm]; exact h1
  · rw [← neg_add, h1]
  · rw [h2]; abel

lemma exists_rows {n : ℕ} (i0 : Fin n) (x : Phase n → ℝ) (hx : x ⬝ᵥ x = 1) :
    ∃ X Y : Matrix (Fin n) (Fin n) ℝ, X * Xᵀ + Y * Yᵀ = 1 ∧ X * Yᵀ = Y * Xᵀ ∧
      (∀ j, X i0 j = x (Sum.inl j)) ∧ (∀ j, Y i0 j = x (Sum.inr j)) := by
  let w : EuclideanSpace ℂ (Fin n) :=
    WithLp.toLp 2 (fun j => (x (Sum.inl j) : ℂ) - Complex.I * (x (Sum.inr j) : ℂ))
  have hw : inner ℂ w w = 1 := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    have : x ⬝ᵥ x = ∑ j, (x (Sum.inl j) ^ 2 + x (Sum.inr j) ^ 2) := by
      rw [dotProduct, Fintype.sum_sum_type, ← Finset.sum_add_distrib]; simp [sq]
    rw [this] at hx
    simp only [dotProduct, w, Pi.star_apply, RCLike.star_def]
    apply Complex.ext
    · simp [Complex.mul_re, ← sq]
      rw [← hx]
    · simp [Complex.mul_im]
      ring_nf; simp
  have hv : Orthonormal ℂ (({i0} : Set (Fin n)).restrict (fun _ => w)) := by
    rw [orthonormal_iff_ite]
    intro i j
    have : i = j := Subsingleton.elim _ _
    simp only [this, if_true]; exact hw
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq (by simp)
  have hon := orthonormal_iff_ite.mp b.orthonormal
  have hre : ∀ i j, ∑ k, ((b i k).re * (b j k).re + (b i k).im * (b j k).im) = if i = j then 1 else 0 := by
    intro i j
    have := congrArg Complex.re (hon j i)
    rw [EuclideanSpace.inner_eq_star_dotProduct] at this
    simp [dotProduct, Complex.mul_re] at this
    rw [eq_comm] at this ⊢
    convert this using 1
    · by_cases h : i = j <;> simp [h, eq_comm]
  have him : ∀ i j, ∑ k, ((b j k).re * (b i k).im - (b j k).im * (b i k).re) = 0 := by
    intro i j
    have := congrArg Complex.im (hon j i)
    rw [EuclideanSpace.inner_eq_star_dotProduct] at this
    simp [dotProduct, Complex.mul_im] at this
    have h0 : (if j = i then (1:ℂ) else 0).im = 0 := by split_ifs <;> simp
    rw [h0] at this
    rw [← this]
    refine Finset.sum_congr rfl fun k _ => by ring
  refine ⟨Matrix.of fun i k => (b i k).re, Matrix.of fun i k => -(b i k).im, ?_, ?_, ?_, ?_⟩
  · ext i j
    simp [Matrix.mul_apply, Matrix.one_apply, ← hre i j, Finset.sum_add_distrib]
  · ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply]
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib, ← him i j]
    refine Finset.sum_congr rfl fun k _ => by ring
  · intro j; simp [hb i0 rfl, w]
  · intro j; simp [hb i0 rfl, w]

lemma conj_diag {m : Type*} [Fintype m] (A B : Matrix m m ℝ) (a : m) :
    (A * B * Aᵀ) a a = A a ⬝ᵥ (B *ᵥ A a) := by
  simp only [Matrix.mul_apply, dotProduct, Matrix.mulVec, Matrix.transpose_apply, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma conj_herm {n : ℕ} (V K : Matrix (Phase n) (Phase n) ℝ) (hV : V.IsHermitian) :
    (K * V * K.transpose).IsHermitian := by
  unfold Matrix.IsHermitian at hV ⊢
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hV, Matrix.mul_assoc]
  simp

lemma crit {n : ℕ} (hn : 0 < n) (V : Matrix (Phase n) (Phase n) ℝ) (hV : V.IsHermitian) :
    PassiveSqueezing V ↔ minimumEigenvalue hn V hV < 1 / 2 := by
  have hne : (Finset.univ : Finset (Phase n)).Nonempty := ⟨Sum.inl ⟨0, hn⟩, Finset.mem_univ _⟩
  show _ ↔ Finset.univ.inf' hne hV.eigenvalues < 1 / 2
  constructor
  · rintro ⟨K, hK, a, ha⟩
    have hB := conj_herm V K hV
    rw [← inf_conj_eq V hV hne K hK.2 hB]
    exact lt_of_le_of_lt (inf_le_diag _ hB hne a) ha
  · intro h
    obtain ⟨x, hx1, hx⟩ := exists_attain V hV hne
    obtain ⟨X, Y, h1, h2, hX, hY⟩ := exists_rows ⟨0, hn⟩ x hx1
    refine ⟨passiveMatrix X Y, passive_of X Y h1 h2, Sum.inl ⟨0, hn⟩, ?_⟩
    have hrow : passiveMatrix X Y (Sum.inl ⟨0, hn⟩) = x := by
      funext k
      rcases k with k | k
      · simp [passiveMatrix, hX]
      · simp [passiveMatrix, hY]
    rw [conj_diag, hrow, hx]
    exact h


lemma c_sq : (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = 1 / 2 := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num

lemma star_c : star ((Real.sqrt 2 : ℂ)⁻¹) = (Real.sqrt 2 : ℂ)⁻¹ := by
  simp [Complex.conj_ofReal]

lemma omega_def (n : ℕ) : canonicalCoordinateMatrix n =
    (Real.sqrt 2 : ℂ)⁻¹ • Matrix.fromBlocks 1 (Complex.I • 1) 1 (-Complex.I • 1) := rfl

lemma omegaH (n : ℕ) : (canonicalCoordinateMatrix n).conjTranspose =
    (Real.sqrt 2 : ℂ)⁻¹ • Matrix.fromBlocks 1 1 (-Complex.I • 1) (Complex.I • 1) := by
  rw [omega_def, conjTranspose_smul, star_c, fromBlocks_conjTranspose]
  simp [conjTranspose_smul]

lemma omegaT (n : ℕ) : (canonicalCoordinateMatrix n).transpose =
    (Real.sqrt 2 : ℂ)⁻¹ • Matrix.fromBlocks 1 1 (Complex.I • 1) (-Complex.I • 1) := by
  rw [omega_def, transpose_smul, fromBlocks_transpose]
  simp

lemma part1 (n : ℕ) : (canonicalCoordinateMatrix n).conjTranspose * canonicalCoordinateMatrix n = 1 := by
  rw [omegaH, omega_def, smul_mul_smul_comm, c_sq, fromBlocks_multiply, ← fromBlocks_one]
  simp [smul_smul]
  rw [fromBlocks_smul, ← fromBlocks_one]
  congr 1 <;> ext i j <;> simp [Matrix.one_apply] <;> split_ifs <;> ring_nf

lemma part2 (n : ℕ) : canonicalCoordinateMatrix n * (canonicalCoordinateMatrix n).conjTranspose = 1 := by
  rw [omegaH, omega_def, smul_mul_smul_comm, c_sq, fromBlocks_multiply, ← fromBlocks_one]
  simp [smul_smul]
  rw [fromBlocks_smul, ← fromBlocks_one]
  congr 1 <;> ext i j <;> simp [Matrix.one_apply] <;> split_ifs <;> ring_nf

lemma isigma (n : ℕ) : Complex.I • complexify (sigma n) = Matrix.fromBlocks 0 (Complex.I • 1) (-Complex.I • 1) 0 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [complexify, sigma, Matrix.one_apply] <;> split_ifs <;> simp

lemma csigma (n : ℕ) : complexify (sigma n) = Matrix.fromBlocks 0 1 (-1) 0 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [complexify, sigma, Matrix.one_apply] <;> split_ifs <;> simp

lemma part3 (n : ℕ) : canonicalCoordinateMatrix n * (Complex.I • complexify (sigma n)) *
    (canonicalCoordinateMatrix n).transpose = complexify (sigma n) := by
  rw [isigma, omegaT, omega_def, csigma]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, c_sq, fromBlocks_multiply]
  simp [smul_smul]
  rw [fromBlocks_smul]
  congr 1 <;> ext i j <;> simp [Matrix.one_apply] <;> split_ifs <;> ring_nf

lemma part4 (n : ℕ) : canonicalCoordinateMatrix n * (Complex.I • complexify (sigma n)) *
    (canonicalCoordinateMatrix n).conjTranspose = sigma3 n := by
  rw [isigma, omegaH, omega_def, sigma3]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, c_sq, fromBlocks_multiply]
  simp [smul_smul]
  rw [fromBlocks_smul]
  congr 1 <;> ext i j <;> simp [Matrix.one_apply] <;> split_ifs <;> ring_nf


lemma cfb {n : ℕ} (A B C D : Matrix (Fin n) (Fin n) ℝ) :
    complexify (Matrix.fromBlocks A B C D) =
      Matrix.fromBlocks (complexify A) (complexify B) (complexify C) (complexify D) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> rfl

lemma part5 {n : ℕ} (A B C D : Matrix (Fin n) (Fin n) ℝ) :
    complexForm (Matrix.fromBlocks A B C D) = (1 / 2 : ℂ) • Matrix.fromBlocks
      (complexify (A + D) + Complex.I • complexify (C - B))
      (complexify (A - D) + Complex.I • complexify (B + C))
      (complexify (A - D) - Complex.I • complexify (B + C))
      (complexify (A + D) + Complex.I • complexify (B - C)) := by
  rw [complexForm, omegaH, omega_def, cfb]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, c_sq, fromBlocks_multiply]
  congr 2 <;> ext i j <;> simp [complexify, Matrix.add_apply, Matrix.sub_apply] <;> ring_nf <;> simp [Complex.I_sq] <;> ring


section New
variable {n : ℕ}

lemma cx_mul {a b c : Type*} [Fintype b] (X : Matrix a b ℝ) (Y : Matrix b c ℝ) :
    complexify (X * Y) = complexify X * complexify Y := by
  ext i j; simp [complexify, Matrix.mul_apply]

lemma cx_add {a b : Type*} (X Y : Matrix a b ℝ) : complexify (X + Y) = complexify X + complexify Y := by
  ext i j; simp [complexify]

lemma cx_smul {a b : Type*} (r : ℝ) (X : Matrix a b ℝ) : complexify (r • X) = (r : ℂ) • complexify X := by
  ext i j; simp [complexify]

lemma cx_one : complexify (1 : Mat n) = 1 := by
  ext i j; simp [complexify, Matrix.one_apply]; split_ifs <;> simp

lemma cx_conjTranspose {a b : Type*} (X : Matrix a b ℝ) : (complexify X)ᴴ = complexify Xᵀ := by
  ext i j; simp [complexify]

lemma one_add_isigma_psd : ((1 : Matrix (Phase n) (Phase n) ℂ) + Complex.I • complexify (sigma n)).PosSemidef := by
  have : (1 : Matrix (Phase n) (Phase n) ℂ) + Complex.I • complexify (sigma n) =
      (Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) (Complex.I • 1) 0 0)ᴴ *
        Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) (Complex.I • 1) 0 0 := by
    rw [isigma, fromBlocks_conjTranspose, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_add]
    simp [conjTranspose_smul, smul_smul, Complex.I_mul_I]
  rw [this]; exact posSemidef_conjTranspose_mul_self _

lemma allowed_half {P : Mat n} (hP : IsPositiveSymplectic P) : Allowed ((1 / 2 : ℝ) • P) := by
  refine ⟨hP.2.smul (by norm_num), ?_⟩
  set R := CFC.sqrt P
  have hRs : PreservesCanonicalForm R := sqrt_symp hP.2 hP.1
  have hRR : R * R = P := CFC.sqrt_mul_sqrt_self P hP.2.posSemidef.nonneg
  have hRt : Rᵀ = R := transpose_of_posSemidef (CFC.sqrt_nonneg P).posSemidef
  have key : complexify P + Complex.I • complexify (sigma n) =
      complexify R * ((1 : Matrix (Phase n) (Phase n) ℂ) + Complex.I • complexify (sigma n)) *
        (complexify R)ᴴ := by
    rw [cx_conjTranspose, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, ← cx_mul, hRt, hRR,
      Matrix.mul_smul, Matrix.smul_mul, ← cx_mul, ← cx_mul]
    congr 3
    have := hRs; unfold PreservesCanonicalForm at this; rw [hRt] at this; exact this.symm
  have h2 : complexify ((1 / 2 : ℝ) • P) + (Complex.I / 2) • complexify (sigma n) =
      (1 / 2 : ℂ) • (complexify P + Complex.I • complexify (sigma n)) := by
    rw [cx_smul, smul_add, smul_smul]; congr 1 <;> [simp; (congr 1; ring)]
  rw [h2, key]
  exact (one_add_isigma_psd.mul_mul_conjTranspose_same _).smul
    (by rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring]; exact Complex.zero_le_real.mpr (by norm_num))

lemma cfH (S : Mat n) : (complexForm S)ᴴ = complexForm Sᵀ := by
  unfold complexForm
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, cx_conjTranspose,
    Matrix.mul_assoc]

lemma cf_symp (S : Mat n) (hS : PreservesCanonicalForm S) :
    complexForm S * sigma3 n * (complexForm S)ᴴ = sigma3 n := by
  rw [cfH, ← part4]
  unfold complexForm
  set O := canonicalCoordinateMatrix n
  have h1 : Oᴴ * O = 1 := part1 n
  calc O * complexify S * Oᴴ * (O * (Complex.I • complexify (sigma n)) * Oᴴ) *
        (O * complexify Sᵀ * Oᴴ)
      = O * (complexify S * (Oᴴ * O) * (Complex.I • complexify (sigma n)) * (Oᴴ * O) *
          complexify Sᵀ) * Oᴴ := by simp only [Matrix.mul_assoc]
    _ = O * (Complex.I • complexify (S * sigma n * Sᵀ)) * Oᴴ := by
        rw [h1, Matrix.mul_one, Matrix.mul_one, cx_mul, cx_mul, Matrix.mul_smul, Matrix.smul_mul]
    _ = O * (Complex.I • complexify (sigma n)) * Oᴴ := by rw [hS]

lemma cf_entries (P : Mat n) (hP : Pᵀ = P) (i j : Fin n) :
    complexForm P (Sum.inl j) (Sum.inl i) = complexForm P (Sum.inr i) (Sum.inr j) ∧
    complexForm P (Sum.inl j) (Sum.inr i) = complexForm P (Sum.inl i) (Sum.inr j) := by
  have hs : ∀ a b, P a b = P b a := fun a b => by rw [← transpose_apply P a b, hP]
  rw [← fromBlocks_toBlocks P, part5]
  simp [Matrix.smul_apply, complexify, toBlocks₁₁, toBlocks₁₂, toBlocks₂₁, toBlocks₂₂]
  refine ⟨?_, ?_⟩
  · rw [hs (Sum.inl j) (Sum.inl i), hs (Sum.inr j) (Sum.inr i), hs (Sum.inr j) (Sum.inl i),
      hs (Sum.inl j) (Sum.inr i)]
  · rw [hs (Sum.inl j) (Sum.inl i), hs (Sum.inr j) (Sum.inr i), hs (Sum.inl j) (Sum.inr i),
      hs (Sum.inr j) (Sum.inl i)]; ring

lemma AB_symm_of (P : Mat n) (hP : Pᵀ = P) (hS : PreservesCanonicalForm P) :
    (noiseA P * noiseB P).IsSymm := by
  have h := cf_symp P hS
  rw [cfH, hP] at h
  set Pc := complexForm P
  have hrel : ∀ i j, ∑ k, Pc (Sum.inl i) (Sum.inl k) * Pc (Sum.inl k) (Sum.inr j) =
      ∑ k, Pc (Sum.inl i) (Sum.inr k) * Pc (Sum.inr k) (Sum.inr j) := by
    intro i j
    have := congrFun (congrFun h (Sum.inl i)) (Sum.inr j)
    simp [Matrix.mul_apply, sigma3, Fintype.sum_sum_type, Matrix.one_apply] at this
    rw [← sub_eq_zero, ← this]; ring
  apply Matrix.IsSymm.ext
  intro i j
  simp only [noiseA, noiseB, Matrix.mul_apply, submatrix_apply]
  rw [hrel i j]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [(cf_entries P hP k j).1, (cf_entries P hP i k).2]; ring

lemma cfA_entry (V : Mat n) (i j : Fin n) : complexForm V (Sum.inl i) (Sum.inl j) =
    (1 / 2 : ℂ) * (((V (Sum.inl i) (Sum.inl j) + V (Sum.inr i) (Sum.inr j) : ℝ) : ℂ) +
      Complex.I * ((V (Sum.inr i) (Sum.inl j) - V (Sum.inl i) (Sum.inr j) : ℝ) : ℂ)) := by
  conv_lhs => rw [← fromBlocks_toBlocks V, part5]
  simp [Matrix.smul_apply, complexify, toBlocks₁₁, toBlocks₁₂, toBlocks₂₁, toBlocks₂₂]

lemma cfB_entry (V : Mat n) (i j : Fin n) : complexForm V (Sum.inl i) (Sum.inr j) =
    (1 / 2 : ℂ) * (((V (Sum.inl i) (Sum.inl j) - V (Sum.inr i) (Sum.inr j) : ℝ) : ℂ) +
      Complex.I * ((V (Sum.inl i) (Sum.inr j) + V (Sum.inr i) (Sum.inl j) : ℝ) : ℂ)) := by
  conv_lhs => rw [← fromBlocks_toBlocks V, part5]
  simp [Matrix.smul_apply, complexify, toBlocks₁₁, toBlocks₁₂, toBlocks₂₁, toBlocks₂₂]

lemma H_bound (V : Mat n) (hV : V ∈ familyH n) (x : Phase n → ℝ) :
    (1 / 2) * (x ⬝ᵥ x) ≤ x ⬝ᵥ (V *ᵥ x) := by
  obtain ⟨-, hB, hA⟩ := hV
  have h1 : ∀ i j, V (Sum.inr i) (Sum.inr j) = V (Sum.inl i) (Sum.inl j) := by
    intro i j
    have := congrArg Complex.re (congrFun (congrFun hB i) j)
    simp [noiseB, cfB_entry] at this
    linarith
  have h2 : ∀ i j, V (Sum.inr i) (Sum.inl j) = - V (Sum.inl i) (Sum.inr j) := by
    intro i j
    have := congrArg Complex.im (congrFun (congrFun hB i) j)
    simp [noiseB, cfB_entry] at this
    linarith
  set z : Fin n → ℂ := fun j => (x (Sum.inl j) : ℂ) + Complex.I * (x (Sum.inr j) : ℂ)
  have hz := hA.dotProduct_mulVec_nonneg z
  have hre := (Complex.nonneg_iff.mp hz).1
  have e1 : (star z ⬝ᵥ ((noiseA V - (1 / 2 : ℂ) • 1) *ᵥ z)).re =
      x ⬝ᵥ (V *ᵥ x) - (1 / 2) * (x ⬝ᵥ x) := by
    simp only [dotProduct, mulVec, Fintype.sum_sum_type, Complex.re_sum, Matrix.sub_apply,
      noiseA, submatrix_apply, cfA_entry, Matrix.smul_apply, Matrix.one_apply, h1, h2, z,
      Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hh : (1 / 2 : ℝ) * (x (Sum.inl j) * x (Sum.inl j) + x (Sum.inr j) * x (Sum.inr j)) =
        ∑ k, if j = k then (1 / 2 : ℝ) * (x (Sum.inl k) * x (Sum.inl j) + x (Sum.inr k) * x (Sum.inr j))
          else 0 := by simp
    rw [hh, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs with hjk
    · subst hjk; simp [Complex.mul_re, Complex.mul_im]; ring
    · simp [Complex.mul_re, Complex.mul_im]; ring
  linarith

lemma P_eq_one (P : Mat n) (hP : P.IsHermitian) (hPt : Pᵀ = P) (hS : PreservesCanonicalForm P)
    (hge : ∀ x : Phase n → ℝ, x ⬝ᵥ x ≤ x ⬝ᵥ (P *ᵥ x)) : P = 1 := by
  have hinv : (sigma n)ᵀ * P * sigma n * P = 1 := by
    unfold PreservesCanonicalForm at hS
    rw [hPt] at hS
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc P, hS, sigmaT_mul_sigma]
  have hev : ∀ j, hP.eigenvalues j = 1 := by
    intro j
    set v : Phase n → ℝ := ⇑(hP.eigenvectorBasis j)
    have hPv : P *ᵥ v = hP.eigenvalues j • v := hP.mulVec_eigenvectorBasis j
    have hvv : v ⬝ᵥ v = 1 := by
      have := hP.eigenvectorBasis.orthonormal.1 j
      rw [EuclideanSpace.norm_eq] at this
      have h2 : ∑ i, ‖(hP.eigenvectorBasis j) i‖ ^ 2 = 1 := by
        have := congrArg (· ^ 2) this
        simp only [one_pow] at this
        rwa [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at this
      rw [dotProduct]
      simpa [sq] using h2
    set l := hP.eigenvalues j
    have hl1 : 1 ≤ l := by
      have := hge v
      rw [hPv, dotProduct_smul, hvv, smul_eq_mul, mul_one] at this
      exact this
    set Q := (sigma n)ᵀ * P * sigma n
    have hQv : Q *ᵥ v = l⁻¹ • v := by
      have h := congrArg (· *ᵥ v) hinv
      simp only [one_mulVec, ← mulVec_mulVec, hPv, mulVec_smul] at h
      have hl0 : l ≠ 0 := by linarith
      calc Q *ᵥ v = l⁻¹ • (l • Q *ᵥ v) := by rw [smul_smul, inv_mul_cancel₀ hl0, one_smul]
        _ = l⁻¹ • v := by rw [h]
    have hQge : 1 ≤ v ⬝ᵥ (Q *ᵥ v) := by
      have h := hge (sigma n *ᵥ v)
      have e1 : (sigma n *ᵥ v) ⬝ᵥ (sigma n *ᵥ v) = v ⬝ᵥ v := by
        rw [dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, sigmaT_mul_sigma, one_mulVec]
      have e2 : (sigma n *ᵥ v) ⬝ᵥ (P *ᵥ (sigma n *ᵥ v)) = v ⬝ᵥ (Q *ᵥ v) := by
        symm
        rw [show Q *ᵥ v = (sigma n)ᵀ *ᵥ (P *ᵥ (sigma n *ᵥ v)) by
          simp only [Q, mulVec_mulVec, Matrix.mul_assoc], dotProduct_mulVec, vecMul_transpose]
      rw [e1, e2, hvv] at h; exact h
    rw [hQv, dotProduct_smul, hvv, smul_eq_mul, mul_one] at hQge
    have hl0 : 0 < l := by linarith
    have : l ≤ 1 := by
      have := (one_le_inv₀ hl0).mp hQge
      exact this
    linarith
  have hspec := hP.spectral_theorem
  have hd : (diagonal (RCLike.ofReal ∘ hP.eigenvalues) : Mat n) = 1 := by
    ext a b; simp [diagonal_apply, Matrix.one_apply, hev]
  rw [hd, map_one] at hspec
  exact hspec

lemma cf_smul (r : ℝ) (P : Mat n) : complexForm (r • P) = (r : ℂ) • complexForm P := by
  unfold complexForm
  rw [cx_smul, Matrix.mul_smul, Matrix.smul_mul]

lemma half_mem_G {P : Mat n} (hP : IsPositiveSymplectic P) : (1 / 2 : ℝ) • P ∈ familyG n := by
  have hPt : Pᵀ = P := transpose_of_posSemidef hP.2.posSemidef
  refine ⟨⟨allowed_half hP, ?_⟩, ?_⟩
  · have hAB := AB_symm_of P hPt hP.1
    have e : noiseA ((1 / 2 : ℝ) • P) * noiseB ((1 / 2 : ℝ) • P) =
        (((1 / 2 : ℝ) : ℂ) * ((1 / 2 : ℝ) : ℂ)) • (noiseA P * noiseB P) := by
      have hs : ∀ (M : Mat n) (c : ℂ) (M' : Matrix (Phase n) (Phase n) ℂ), M' = complexForm M →
          ∀ f g : Fin n → Phase n, (c • M').submatrix f g = c • M'.submatrix f g :=
        fun _ _ _ _ _ _ => by ext; simp
      simp only [noiseA, noiseB, cf_smul, hs P _ _ rfl, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [e]; exact hAB.smul _
  · rw [smul_smul]; norm_num; exact hP

lemma H_no_sq {V : Mat n} (hV : V ∈ familyH n) : ¬ PassiveSqueezing V := by
  rintro ⟨K, hK, a, ha⟩
  have hKK : K * Kᵀ = 1 := mul_eq_one_comm.mp hK.2
  have hx : K a ⬝ᵥ K a = 1 := by
    have := congrFun (congrFun hKK a) a
    simp only [Matrix.mul_apply, transpose_apply, Matrix.one_apply_eq] at this
    rw [dotProduct]; exact this
  have := H_bound V hV (K a)
  rw [hx, ← conj_diag] at this
  linarith

lemma G_sq (hn : 0 < n) {V : Mat n} (hV : V ∈ familyG n) (hne : V ≠ (1 / 2 : ℝ) • 1) :
    PassiveSqueezing V := by
  have hVh : V.IsHermitian := hV.1.1.1.isHermitian
  by_contra hns
  rw [crit hn V hVh] at hns
  push Not at hns
  have hne' : (Finset.univ : Finset (Phase n)).Nonempty := ⟨Sum.inl ⟨0, hn⟩, Finset.mem_univ _⟩
  have hge : ∀ x : Phase n → ℝ, x ⬝ᵥ x ≤ x ⬝ᵥ (((2 : ℝ) • V) *ᵥ x) := by
    intro x
    have h1 := inf_mul_le V hVh hne' x
    have h2 : 0 ≤ x ⬝ᵥ x := by rw [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    have h3 : (1 / 2) * (x ⬝ᵥ x) ≤ minimumEigenvalue hn V hVh * (x ⬝ᵥ x) :=
      mul_le_mul_of_nonneg_right hns h2
    rw [smul_mulVec, dotProduct_smul, smul_eq_mul]
    have : minimumEigenvalue hn V hVh = Finset.univ.inf' hne' hVh.eigenvalues := rfl
    rw [this] at h3
    linarith
  have hP := hV.2
  have hP1 := P_eq_one _ hP.2.isHermitian (transpose_of_posSemidef hP.2.posSemidef) hP.1 hge
  apply hne
  rw [← hP1, smul_smul]; norm_num

end New

end X4SF

open QAlgorithms.Papers.Independent.Claimed50.P41 X4SF in
theorem solution (n : ℕ) (hn : 0 < n) :
    familyH n ⊆ familyK n ∧ familyG n ⊆ familyK n ∧
    familyK n ⊆ {V | Allowed V} ∧
    (∀ P : Matrix (Phase n) (Phase n) ℝ, IsPositiveSymplectic P →
      (1 / 2 : ℝ) • P ∈ familyG n) ∧
    (∀ V ∈ familyH n, ¬ PassiveSqueezing V) ∧
    (∀ V ∈ familyG n, V ≠ (1 / 2 : ℝ) • (1 : Matrix (Phase n) (Phase n) ℝ) →
      PassiveSqueezing V) ∧
    familyH n ∩ familyG n = {(1 / 2 : ℝ) • (1 : Matrix (Phase n) (Phase n) ℝ)} := by
  have hG1 : (1 / 2 : ℝ) • (1 : Matrix (Phase n) (Phase n) ℝ) ∈ familyG n :=
    half_mem_G ⟨by simp [PreservesCanonicalForm], Matrix.PosDef.one⟩
  have hcf : complexForm ((1 / 2 : ℝ) • (1 : Matrix (Phase n) (Phase n) ℝ)) = (1 / 2 : ℂ) • 1 := by
    rw [cf_smul]; unfold complexForm; rw [cx_one, Matrix.mul_one, part2]; norm_num
  have hH1 : (1 / 2 : ℝ) • (1 : Matrix (Phase n) (Phase n) ℝ) ∈ familyH n := by
    refine ⟨hG1.1, ?_, ?_⟩
    · ext i j; simp only [noiseB, hcf]; simp
    · have : noiseA ((1 / 2 : ℝ) • (1 : Matrix (Phase n) (Phase n) ℝ)) - (1 / 2 : ℂ) • 1 = 0 := by
        ext i j; simp only [noiseA, hcf]; simp [Matrix.one_apply]
      rw [this]; exact Matrix.PosSemidef.zero
  refine ⟨fun V hV => hV.1, fun V hV => hV.1, fun V hV => hV.1, fun P hP => half_mem_G hP,
    fun V hV => H_no_sq hV, fun V hV hne => G_sq hn hV hne, ?_⟩
  ext V
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hH, hG⟩
    by_contra hne
    exact H_no_sq hH (G_sq hn hG hne)
  · rintro rfl; exact ⟨hH1, hG1⟩

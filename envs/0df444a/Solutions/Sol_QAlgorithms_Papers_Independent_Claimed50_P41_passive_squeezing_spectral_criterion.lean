-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P41.passive_squeezing_spectral_criterion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:57:43.952624+00:00
-- url     : https://prove2.me/submissions/3b18ffe4-aaf7-41ba-a3b4-cf157a8635bd

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P41

open scoped ComplexOrder

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

namespace X4PassCrit

open Matrix

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

open QAlgorithms.Papers.Independent.Claimed50.P41

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

end X4PassCrit

open QAlgorithms.Papers.Independent.Claimed50.P41 in
theorem solution (n : ℕ) (hn : 0 < n)
    (V : Matrix (Phase n) (Phase n) ℝ) (hV : Allowed V) :
    (PassiveSqueezing V ↔ minimumEigenvalue hn V hV.1.isHermitian < 1 / 2) ∧
    (∀ K : Matrix (Phase n) (Phase n) ℝ, IsPassive K →
      (PassiveSqueezing (K * V * K.transpose) ↔ PassiveSqueezing V)) := by
  refine ⟨X4PassCrit.crit hn V _, fun K hK => ?_⟩
  have hB := X4PassCrit.conj_herm V K hV.1.isHermitian
  rw [X4PassCrit.crit hn _ hB, X4PassCrit.crit hn V hV.1.isHermitian]
  have hne : (Finset.univ : Finset (Phase n)).Nonempty := ⟨Sum.inl ⟨0, hn⟩, Finset.mem_univ _⟩
  show Finset.univ.inf' hne hB.eigenvalues < 1 / 2 ↔ Finset.univ.inf' hne _ < 1 / 2
  rw [X4PassCrit.inf_conj_eq V hV.1.isHermitian hne K hK.2 hB]

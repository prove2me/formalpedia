-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P41.manifest_implies_invariant_squeezing
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:52:33.34866+00:00
-- url     : https://prove2.me/submissions/32a6e761-ee99-4510-8b3e-d83b2ba0e462

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P41

open scoped ComplexOrder

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

namespace X4ManifestSq

open Matrix

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

open QAlgorithms.Papers.Independent.Claimed50.P41

/-- The explicit one-mode counterexample. -/
noncomputable def Vex : Matrix (Phase 1) (Phase 1) ℝ := Matrix.of fun i j => if i = j then (9 / 16 : ℝ) else 1 / 4

lemma sum_phase1 (f : Phase 1 → ℝ) : ∑ i, f i = f (Sum.inl 0) + f (Sum.inr 0) := by
  simp [Fintype.sum_sum_type]

lemma sum_phase1C (f : Phase 1 → ℂ) : ∑ i, f i = f (Sum.inl 0) + f (Sum.inr 0) := by
  simp [Fintype.sum_sum_type]

lemma Vex_herm : Vex.IsHermitian := by
  ext i j
  simp only [Vex, conjTranspose_apply, of_apply, star_trivial]
  by_cases h : i = j
  · simp [h]
  · simp [h, Ne.symm h]

lemma Vex_posDef : Vex.PosDef := by
  refine PosDef.of_dotProduct_mulVec_pos Vex_herm fun x hx => ?_
  simp only [star_trivial, dotProduct, mulVec, sum_phase1, Vex, of_apply]
  simp
  have : x (Sum.inl 0) ≠ 0 ∨ x (Sum.inr 0) ≠ 0 := by
    by_contra h
    push Not at h
    apply hx
    funext i
    rcases i with i | i <;> fin_cases i <;> simp [h.1, h.2]
  rcases this with h | h
  · have := sq_pos_of_ne_zero h
    nlinarith [sq_nonneg (x (Sum.inl 0) + x (Sum.inr 0)), sq_nonneg (x (Sum.inr 0))]
  · have := sq_pos_of_ne_zero h
    nlinarith [sq_nonneg (x (Sum.inl 0) + x (Sum.inr 0)), sq_nonneg (x (Sum.inl 0))]

/-- Cholesky factor of `Vex + (i/2) sigma`. -/
noncomputable def Bch : Matrix (Phase 1) (Phase 1) ℂ := Matrix.of fun i j =>
  match i, j with
  | Sum.inl _, Sum.inl _ => 3 / 4
  | Sum.inl _, Sum.inr _ => 1 / 3 + (2 / 3) * Complex.I
  | Sum.inr _, Sum.inl _ => 0
  | Sum.inr _, Sum.inr _ => 1 / 12

lemma Vex_allowed : Allowed Vex := by
  refine ⟨Vex_posDef, ?_⟩
  have : complexify Vex + (Complex.I / 2) • complexify (sigma 1) = Bchᴴ * Bch := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [complexify, Vex, sigma, Bch, Matrix.mul_apply, Complex.ext_iff, map_div₀, map_ofNat, Complex.div_ofNat_re, Complex.div_ofNat_im] <;> norm_num
  rw [this]
  exact posSemidef_conjTranspose_mul_self _

lemma minEig_eq {n : ℕ} (hn : 0 < n) (V : Matrix (Phase n) (Phase n) ℝ) (hV : V.IsHermitian) :
    minimumEigenvalue hn V hV = Finset.univ.inf' ⟨Sum.inl ⟨0, hn⟩, Finset.mem_univ _⟩ hV.eigenvalues := rfl

lemma minEig_le {n : ℕ} (hn : 0 < n) (V : Matrix (Phase n) (Phase n) ℝ) (hV : V.IsHermitian)
    (x : Phase n → ℝ) (hx : x ⬝ᵥ x = 1) : minimumEigenvalue hn V hV ≤ x ⬝ᵥ (V *ᵥ x) := by
  have := inf_mul_le V hV ⟨Sum.inl ⟨0, hn⟩, Finset.mem_univ _⟩ x
  rw [hx, mul_one] at this
  exact this

lemma minEig_le_diag {n : ℕ} (hn : 0 < n) (V : Matrix (Phase n) (Phase n) ℝ) (hV : V.IsHermitian)
    (a : Phase n) : minimumEigenvalue hn V hV ≤ V a a := by
  have := minEig_le hn V hV (Pi.single a 1) (by simp)
  simpa using this

end X4ManifestSq

open QAlgorithms.Papers.Independent.Claimed50.P41 X4ManifestSq in
theorem solution :
    (∀ (V : Matrix (Phase 1) (Phase 1) ℝ) (hV : Allowed V),
      (Real.sqrt (V (Sum.inl 0) (Sum.inl 0)) < (Real.sqrt 2)⁻¹ ∨
       Real.sqrt (V (Sum.inr 0) (Sum.inr 0)) < (Real.sqrt 2)⁻¹) →
      minimumEigenvalue (by decide : 0 < 1) V hV.1.isHermitian < 1 / 2) ∧
    (∃ (V : Matrix (Phase 1) (Phase 1) ℝ) (hV : Allowed V),
      minimumEigenvalue (by decide : 0 < 1) V hV.1.isHermitian < 1 / 2 ∧
        ¬ ManifestSqueezing V) ∧
    (∀ (V : Matrix (Phase 1) (Phase 1) ℝ) (hV : Allowed V)
      (K : Matrix (Phase 1) (Phase 1) ℝ), IsPassive K →
      ∃ hW : (K * V * K.transpose).IsHermitian,
        minimumEigenvalue (by decide : 0 < 1) (K * V * K.transpose) hW =
          minimumEigenvalue (by decide : 0 < 1) V hV.1.isHermitian) := by
  have key : ∀ x : ℝ, 0 ≤ x → Real.sqrt x < (Real.sqrt 2)⁻¹ → x < 1 / 2 := by
    intro x hx h
    rw [← Real.sqrt_inv, Real.sqrt_lt_sqrt_iff hx] at h
    linarith
  refine ⟨?_, ?_, ?_⟩
  · intro V hV h
    rcases h with h | h
    · exact lt_of_le_of_lt (minEig_le_diag _ V _ _) (key _ hV.1.diag_pos.le h)
    · exact lt_of_le_of_lt (minEig_le_diag _ V _ _) (key _ hV.1.diag_pos.le h)
  · refine ⟨Vex, Vex_allowed, ?_, ?_⟩
    · set x : Phase 1 → ℝ := fun i => match i with
        | Sum.inl _ => (Real.sqrt 2)⁻¹
        | Sum.inr _ => -(Real.sqrt 2)⁻¹
      have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have hs : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = 1 / 2 := by
        rw [← mul_inv, ← sq, h2]; norm_num
      have hx : x ⬝ᵥ x = 1 := by
        simp only [dotProduct, sum_phase1, x]
        rw [neg_mul_neg, hs]; norm_num
      have := minEig_le (by decide : 0 < 1) Vex Vex_allowed.1.isHermitian x hx
      refine lt_of_le_of_lt this ?_
      simp only [dotProduct, Matrix.mulVec, sum_phase1, x, Vex, Matrix.of_apply]
      simp
      nlinarith [hs]
    · rintro ⟨a, ha⟩
      simp [Vex] at ha
      norm_num at ha
  · intro V hV K hK
    have hB : (K * V * K.transpose).IsHermitian := by
      have := hV.1.isHermitian
      unfold Matrix.IsHermitian at this ⊢
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, this, Matrix.mul_assoc]
      simp
    exact ⟨hB, inf_conj_eq V hV.1.isHermitian _ K hK.2 hB⟩

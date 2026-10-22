-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P41.one_mode_uncertainty
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T09:27:07.00999+00:00
-- url     : https://prove2.me/submissions/6f7b0bfb-b5ae-4a89-867a-65d7c6f3b9d3

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P41
noncomputable section

open MeasureTheory

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

open QAlgorithms.Papers.Independent.Claimed50.P41

lemma g68k_sigma (n : ℕ) : sigma n = -Matrix.J (Fin n) ℝ := by
  simp [sigma, Matrix.J, Matrix.fromBlocks_neg]

lemma g68k_pres_iff {n : ℕ} (S : Matrix (Phase n) (Phase n) ℝ) :
    PreservesCanonicalForm S ↔ S ∈ Matrix.symplecticGroup (Fin n) ℝ := by
  rw [SymplecticGroup.mem_iff, PreservesCanonicalForm, g68k_sigma]
  simp [Matrix.mul_neg, Matrix.neg_mul]

lemma g68k_sigma_inv (n : ℕ) : (sigma n)⁻¹ = Matrix.J (Fin n) ℝ := by
  rw [g68k_sigma]
  apply Matrix.inv_eq_left_inv
  simp [Matrix.mul_neg, Matrix.J_squared]

lemma g68k_bracket {n : ℕ} (S : Matrix (Phase n) (Phase n) ℝ) (a b : Phase n) :
    linearCanonicalBracket S a b = (S * sigma n * S.transpose) a b := by
  simp only [linearCanonicalBracket, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

lemma g68k_det2 {R : Type*} [CommRing R] (M : Matrix (Phase 1) (Phase 1) R) :
    M.det = M (Sum.inl 0) (Sum.inl 0) * M (Sum.inr 0) (Sum.inr 0) -
      M (Sum.inl 0) (Sum.inr 0) * M (Sum.inr 0) (Sum.inl 0) := by
  rw [← Matrix.det_reindex_self finSumFinEquiv M, Matrix.det_fin_two]
  simp [Matrix.reindex_apply]
  rfl

lemma g68k_symm1 (W : Matrix (Phase 1) (Phase 1) ℝ) (hW : W.IsSymm) :
    W (Sum.inr 0) (Sum.inl 0) = W (Sum.inl 0) (Sum.inr 0) := by
  have := congrFun (congrFun hW (Sum.inl 0)) (Sum.inr 0)
  simpa [Matrix.transpose_apply] using this

lemma g68k_quad_real (W : Matrix (Phase 1) (Phase 1) ℝ) (x : Phase 1 → ℝ) :
    dotProduct (star x) (W.mulVec x) = W (Sum.inl 0) (Sum.inl 0) * x (Sum.inl 0) ^ 2 +
      (W (Sum.inl 0) (Sum.inr 0) + W (Sum.inr 0) (Sum.inl 0)) * x (Sum.inl 0) * x (Sum.inr 0) +
      W (Sum.inr 0) (Sum.inr 0) * x (Sum.inr 0) ^ 2 := by
  simp [dotProduct, Matrix.mulVec, Fintype.sum_sum_type]
  ring

lemma g68k_allowed_iff (W : Matrix (Phase 1) (Phase 1) ℝ) (hW : W.IsSymm) :
    Allowed W ↔ 0 < W (Sum.inl 0) (Sum.inl 0) ∧ 1 / 4 ≤ W.det := by
  have hs := g68k_symm1 W hW
  rw [g68k_det2, hs]
  set a := W (Sum.inl 0) (Sum.inl 0)
  set b := W (Sum.inl 0) (Sum.inr 0)
  set c := W (Sum.inr 0) (Sum.inr 0)
  set M := complexify W + (Complex.I / 2) • complexify (sigma 1) with hM
  have Mll : M (Sum.inl 0) (Sum.inl 0) = a := by simp [hM, complexify, sigma, a]
  have Mrr : M (Sum.inr 0) (Sum.inr 0) = c := by simp [hM, complexify, sigma, c]
  have Mlr : M (Sum.inl 0) (Sum.inr 0) = b + Complex.I / 2 := by simp [hM, complexify, sigma, b]
  have Mrl : M (Sum.inr 0) (Sum.inl 0) = b - Complex.I / 2 := by
    simp [hM, complexify, sigma, b, hs]; ring
  constructor
  · rintro ⟨hpd, hpsd⟩
    refine ⟨hpd.diag_pos, ?_⟩
    have h := hpsd.det_nonneg
    rw [← hM, g68k_det2, Mll, Mrr, Mlr, Mrl] at h
    have : (a : ℂ) * c - (b + Complex.I / 2) * (b - Complex.I / 2) = ((a * c - b * b - 1/4 : ℝ) : ℂ) := by
      push_cast; ring_nf; rw [Complex.I_sq]; ring
    rw [this, Complex.zero_le_real] at h
    linarith
  · rintro ⟨ha, hdet⟩
    refine ⟨?_, ?_⟩
    · rw [Matrix.posDef_iff_dotProduct_mulVec]
      refine ⟨(by ext i j; simp [Matrix.conjTranspose_apply]; exact congrFun (congrFun hW i) j), fun x hx => ?_⟩
      rw [g68k_quad_real, hs]
      have hx' : x (Sum.inl 0) ≠ 0 ∨ x (Sum.inr 0) ≠ 0 := by
        by_contra h
        push_neg at h
        apply hx; funext i; rcases i with i | i <;> fin_cases i <;> simp [h.1, h.2]
      have key : a * (a * x (Sum.inl 0) ^ 2 + (b + b) * x (Sum.inl 0) * x (Sum.inr 0) + c * x (Sum.inr 0) ^ 2)
          = (a * x (Sum.inl 0) + b * x (Sum.inr 0)) ^ 2 + (a * c - b * b) * x (Sum.inr 0) ^ 2 := by ring
      have : 0 < a * (a * x (Sum.inl 0) ^ 2 + (b + b) * x (Sum.inl 0) * x (Sum.inr 0) + c * x (Sum.inr 0) ^ 2) := by
        rw [key]
        by_cases h2 : x (Sum.inr 0) = 0
        · have h1 : x (Sum.inl 0) ≠ 0 := by tauto
          rw [h2]; simp; positivity
        · have : 0 < (a * c - b * b) * x (Sum.inr 0) ^ 2 := by
            apply mul_pos (by linarith); positivity
          positivity
      exact pos_of_mul_pos_right this ha.le
    · rw [Matrix.posSemidef_iff_dotProduct_mulVec, ← hM]
      have hH : M.IsHermitian := by
        ext i j
        rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
          simp [Matrix.conjTranspose_apply, Mll, Mrr, Mlr, Mrl, Complex.conj_ofReal] <;>
          simp [Complex.ext_iff] <;> norm_num
      refine ⟨hH, fun x => ?_⟩
      have hq : dotProduct (star x) (M.mulVec x) = (((Complex.normSq (a * x (Sum.inl 0) + (b + Complex.I / 2) * x (Sum.inr 0)) +
          (a * c - b * b - 1 / 4) * Complex.normSq (x (Sum.inr 0))) / a : ℝ) : ℂ) := by
        simp only [dotProduct, Matrix.mulVec, Fintype.sum_sum_type, Finset.univ_unique,
          Fin.default_eq_zero, Finset.sum_singleton, Mll, Mrr, Mlr, Mrl, Pi.star_apply]
        apply Complex.ext <;>
        simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im] <;> field_simp <;> ring
      rw [hq, Complex.zero_le_real]
      apply div_nonneg _ ha.le
      have := Complex.normSq_nonneg (x (Sum.inr 0))
      have := Complex.normSq_nonneg (a * x (Sum.inl 0) + (b + Complex.I / 2) * x (Sum.inr 0))
      nlinarith



/-- PDF pp.31–32, (10.2)–(10.3): one-mode uncertainty for matrices in
the source family S (11.1); deltas are square roots of variances. -/
theorem solution (V : Matrix (Phase 1) (Phase 1) ℝ) (hV : Allowed V) :
    Real.sqrt (V (Sum.inl 0) (Sum.inl 0)) * Real.sqrt (V (Sum.inr 0) (Sum.inr 0)) ≥ 1 / 2 ∧
    V.det = V (Sum.inl 0) (Sum.inl 0) * V (Sum.inr 0) (Sum.inr 0) -
      V (Sum.inl 0) (Sum.inr 0) ^ 2 ∧ V.det ≥ 1 / 4 ∧
    (∀ W : Matrix (Phase 1) (Phase 1) ℝ, W.IsSymm →
      (Allowed W ↔ 0 < W (Sum.inl 0) (Sum.inl 0) ∧ 1 / 4 ≤ W.det)) ∧
    (∀ S : Matrix (Phase 1) (Phase 1) ℝ, PreservesCanonicalForm S → (S * V * S.transpose).det = V.det) := by
  have hsymm : V.IsSymm := by
    ext i j
    have := hV.1.1.apply i j
    simpa using this
  have hs := g68k_symm1 V hsymm
  have hdetf : V.det = V (Sum.inl 0) (Sum.inl 0) * V (Sum.inr 0) (Sum.inr 0) -
      V (Sum.inl 0) (Sum.inr 0) ^ 2 := by rw [g68k_det2, hs]; ring
  have hA := (g68k_allowed_iff V hsymm).1 hV
  have hd : V.det ≥ 1 / 4 := hA.2
  refine ⟨?_, hdetf, hd, fun W hW => g68k_allowed_iff W hW, fun S hS => ?_⟩
  · rw [← Real.sqrt_mul hA.1.le]
    rw [ge_iff_le, Real.le_sqrt (by norm_num)]
    all_goals nlinarith [sq_nonneg (V (Sum.inl 0) (Sum.inr 0))]
  · rw [g68k_pres_iff] at hS
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, SymplecticGroup.det_eq_one hS]
    ring



end

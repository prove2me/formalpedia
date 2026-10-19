-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P62.rank_one_purification
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:49:21.472916+00:00
-- url     : https://prove2.me/submissions/021d16b9-db3f-4231-a076-9fa32495162b

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P62
open scoped ComplexConjugate

noncomputable section

private def column {g : ℕ} (u : EuclideanSpace ℂ (Fin 2 × Fin g))
    (a : Fin g) : EuclideanSpace ℂ (Fin 2) :=
  WithLp.toLp 2 (fun i => u (i, a))

private lemma column_inner {g : ℕ} (u v : EuclideanSpace ℂ (Fin 2 × Fin g))
    (a b : Fin g) :
    inner ℂ (column u a) (column v b) = partialCross v u b a := by
  simp [column, EuclideanSpace.inner_eq_star_dotProduct, partialCross, dotProduct]

private lemma two_basis_decomposition (x y z : EuclideanSpace ℂ (Fin 2))
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : inner ℂ x y = 0) :
    z = (inner ℂ x z) • x + (inner ℂ y z) • y := by
  let f : Fin 2 → EuclideanSpace ℂ (Fin 2) := ![x, y]
  have hon : Orthonormal ℂ f := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j
    · simpa [f] using (inner_self_eq_one_of_norm_eq_one hx : inner ℂ x x = 1)
    · simpa [f] using hxy
    · simpa [f] using (inner_eq_zero_symm.mp hxy : inner ℂ y x = 0)
    · simpa [f] using (inner_self_eq_one_of_norm_eq_one hy : inner ℂ y y = 1)
  have hsp := hon.linearIndependent.span_eq_top_of_card_eq_finrank (by simp)
  let b := OrthonormalBasis.mk hon hsp.ge
  have hb : (b : Fin 2 → EuclideanSpace ℂ (Fin 2)) = f :=
    OrthonormalBasis.coe_mk hon hsp.ge
  have h := b.sum_repr z
  simpa [OrthonormalBasis.repr_apply_apply, hb, f, Fin.sum_univ_two] using h.symm

-- Equal reduced operators and zero cross operator force a common one-dimensional factor.
theorem solution (g : ℕ) (_hg : 0 < g)
    (u v : EuclideanSpace ℂ (Fin 2 × Fin g)) (hu : u ≠ 0) (_hv : v ≠ 0)
    (heq : partialCross u u = partialCross v v) (hcross : partialCross u v = 0) :
    ∃ w : EuclideanSpace ℂ (Fin g), w ≠ 0 ∧
      ∃ x y : EuclideanSpace ℂ (Fin 2), IsState x ∧ IsState y ∧ inner ℂ x y = 0 ∧
        u = tensorVec x w ∧ v = tensorVec y w := by
  classical
  have hsame (a b : Fin g) :
      inner ℂ (column u a) (column u b) = inner ℂ (column v a) (column v b) := by
    simpa only [column_inner] using congrFun (congrFun heq b) a
  have hzero (a b : Fin g) : inner ℂ (column v a) (column u b) = 0 := by
    simpa only [column_inner, Matrix.zero_apply] using congrFun (congrFun hcross b) a
  obtain ⟨a, ha⟩ : ∃ a : Fin g, column u a ≠ 0 := by
    by_contra h
    push Not at h
    apply hu
    ext ⟨i, a⟩
    exact congrArg (fun z : EuclideanSpace ℂ (Fin 2) => z i) (h a)
  let r : ℝ := ‖column u a‖
  have hr : 0 < r := norm_pos_iff.mpr ha
  have hvnorm : ‖column v a‖ = r := by
    have h := congrArg (RCLike.re : ℂ → ℝ) (hsame a a)
    rw [inner_self_eq_norm_sq, inner_self_eq_norm_sq] at h
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h.symm
  let c : ℂ := (r : ℂ)⁻¹
  let x := c • column u a
  let y := c • column v a
  have hx : ‖x‖ = 1 := by
    rw [norm_smul]
    change ‖(r : ℂ)⁻¹‖ * r = 1
    simp [Complex.norm_real, abs_of_pos hr, inv_mul_cancel₀ hr.ne']
  have hy : ‖y‖ = 1 := by
    simp [y, c, norm_smul, hvnorm, Complex.norm_real, abs_of_pos hr, inv_mul_cancel₀ hr.ne']
  have hxy : inner ℂ x y = 0 := by
    have h : inner ℂ (column u a) (column v a) = 0 := inner_eq_zero_symm.mp (hzero a a)
    simp [x, y, h]
  let w : EuclideanSpace ℂ (Fin g) := WithLp.toLp 2 (fun b => inner ℂ x (column u b))
  have hu_col (b : Fin g) : column u b = (w b) • x := by
    have h : inner ℂ y (column u b) = 0 := by
      simp [y, hzero]
    simpa [w, h] using two_basis_decomposition x y (column u b) hx hy hxy
  have hv_col (b : Fin g) : column v b = (w b) • y := by
    have h : inner ℂ x (column v b) = 0 := by
      have hz := inner_eq_zero_symm.mp (hzero b a)
      simp [x, hz]
    have hs : inner ℂ y (column v b) = w b := by
      change inner ℂ (c • column v a) (column v b) =
        inner ℂ (c • column u a) (column u b)
      simp only [inner_smul_left, hsame]
    simpa [h, hs] using two_basis_decomposition x y (column v b) hx hy hxy
  have hw : w ≠ 0 := by
    intro h
    apply hu
    ext ⟨i, b⟩
    have he := congrArg (fun z : EuclideanSpace ℂ (Fin 2) => z i) (hu_col b)
    simpa [column, h] using he
  refine ⟨w, hw, x, y, hx, hy, hxy, ?_, ?_⟩
  · ext ⟨i, b⟩
    have he := congrArg (fun z : EuclideanSpace ℂ (Fin 2) => z i) (hu_col b)
    simpa [column, tensorVec, mul_comm] using he
  · ext ⟨i, b⟩
    have he := congrArg (fun z : EuclideanSpace ℂ (Fin 2) => z i) (hv_col b)
    simpa [column, tensorVec, mul_comm] using he

#print axioms solution

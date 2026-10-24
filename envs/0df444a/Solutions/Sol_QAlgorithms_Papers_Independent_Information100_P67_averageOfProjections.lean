-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P67.averageOfProjections
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T06:04:13.219732+00:00
-- url     : https://prove2.me/submissions/c24d8f24-52f2-4daf-801e-fdb93dc51c40

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder InnerProductSpace

namespace X7AP

open Matrix

/-- quadratic form bound for real matrices -/
lemma quad_le {X : Type*} [Fintype X] [DecidableEq X] (M : Matrix X X ℝ) (p : X → ℝ) :
    ∑ x, ∑ y, M x y * (p x * p y) ≤
      (@Norm.norm (Matrix X X ℝ) Matrix.instL2OpNormedAddCommGroup.toNorm M) * ∑ x, p x ^ 2 := by
  have h1 : ∑ x, ∑ y, M x y * (p x * p y) =
      ⟪(WithLp.toLp 2 p : EuclideanSpace ℝ X), toEuclideanCLM (𝕜 := ℝ) M (WithLp.toLp 2 p)⟫_ℝ := by
    rw [inner_toEuclideanCLM]
    simp only [dotProduct, mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro x _; apply Finset.sum_congr rfl; intro y _; ring
  have h2 : ‖(WithLp.toLp 2 p : EuclideanSpace ℝ X)‖ ^ 2 = ∑ x, p x ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]; simp
  rw [h1, ← h2]
  set z : EuclideanSpace ℝ X := WithLp.toLp 2 p
  calc ⟪z, toEuclideanCLM (𝕜 := ℝ) M z⟫_ℝ ≤ ‖z‖ * ‖toEuclideanCLM (𝕜 := ℝ) M z‖ :=
        real_inner_le_norm _ _
    _ ≤ ‖z‖ * (‖toEuclideanCLM (𝕜 := ℝ) M‖ * ‖z‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ = _ := by rw [← Matrix.cstar_norm_def]; ring


lemma re_gram_le {X A : Type*} [Fintype X] [DecidableEq X] [Fintype A] (M : Matrix X X ℝ)
    (a : X → EuclideanSpace ℂ A) :
    (∑ x, ∑ y, (M x y : ℂ) * ⟪a x, a y⟫_ℂ).re ≤
      (@Norm.norm (Matrix X X ℝ) Matrix.instL2OpNormedAddCommGroup.toNorm M) * ∑ x, ‖a x‖ ^ 2 := by
  have e1 : (∑ x, ∑ y, (M x y : ℂ) * ⟪a x, a y⟫_ℂ).re =
      ∑ k, (∑ x, ∑ y, M x y * ((a x k).re * (a y k).re) +
        ∑ x, ∑ y, M x y * ((a x k).im * (a y k).im)) := by
    have l : (∑ x, ∑ y, (M x y : ℂ) * ⟪a x, a y⟫_ℂ).re =
        ∑ x, ∑ y, ∑ k, (M x y * ((a x k).re * (a y k).re) + M x y * ((a x k).im * (a y k).im)) := by
      simp only [Complex.re_sum, PiLp.inner_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ =>
        Finset.sum_congr rfl (fun k _ => ?_)))
      simp [Complex.mul_re, RCLike.inner_apply]; ring
    rw [l]
    simp only [← Finset.sum_add_distrib]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    exact Finset.sum_comm
  have e2 : ∑ x, ‖a x‖ ^ 2 = ∑ k, (∑ x, (a x k).re ^ 2 + ∑ x, (a x k).im ^ 2) := by
    simp only [EuclideanSpace.norm_sq_eq, ← Finset.sum_add_distrib]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro x _
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  rw [e1, e2, Finset.mul_sum]
  apply Finset.sum_le_sum; intro k _
  rw [mul_add]
  exact add_le_add (quad_le M _) (quad_le M _)


open QAlgorithms QAlgorithms.Papers.Independent.Information100.P67

lemma main_bound {A : Type*} [Fintype A] [DecidableEq A] {n : ℕ}
    (P : (Fin n → Bool) → Matrix A A ℂ)
    (hP : ∀ x, (P x)ᴴ = P x ∧ P x * P x = P x)
    (W : Matrix (Fin n → Bool) (Fin n → Bool) ℝ) (hW : W.transpose = W)
    (zeta ell eta : ℝ) (hz : 0 ≤ zeta) (hl : 0 ≤ ell) (he : 0 ≤ eta)
    (happrox : specNorm (W - uniformLabelMatrix n) ≤ zeta)
    (hrow : ∀ x, ∑ y, |W x y| ≤ ell)
    (hoverlap : ∀ x y, W x y ≠ 0 → specNorm (P x * P y) ≤ eta)
    (v : EuclideanSpace ℂ A) :
    ‖toEuclideanCLM (𝕜 := ℂ) (((((2 : ℝ) ^ n)⁻¹ : ℂ)) • ∑ x, P x) v‖ ≤
      min 1 (zeta + ell * eta) * ‖v‖ := by
  set N : ℝ := (2 : ℝ) ^ n with hN
  have hNpos : 0 < N := by positivity
  have hcard : (Fintype.card (Fin n → Bool) : ℝ) = N := by simp [hN]
  set Q : (Fin n → Bool) → (EuclideanSpace ℂ A →L[ℂ] EuclideanSpace ℂ A) :=
    fun x => toEuclideanCLM (𝕜 := ℂ) (P x) with hQ
  have hsa : ∀ x u w, ⟪Q x u, w⟫_ℂ = ⟪u, Q x w⟫_ℂ := by
    intro x u w
    have : ContinuousLinearMap.adjoint (Q x) = Q x := by
      have h := map_star (toEuclideanCLM (n := A) (𝕜 := ℂ)) (P x)
      rw [Matrix.star_eq_conjTranspose, (hP x).1] at h
      rw [ContinuousLinearMap.star_eq_adjoint] at h
      exact h.symm
    rw [← ContinuousLinearMap.adjoint_inner_right, this]
  have hid : ∀ x u, Q x (Q x u) = Q x u := by
    intro x u
    have h := map_mul (toEuclideanCLM (n := A) (𝕜 := ℂ)) (P x) (P x)
    rw [(hP x).2] at h
    show (Q x * Q x) u = Q x u
    simp only [hQ]; rw [← h]
  set a : (Fin n → Bool) → EuclideanSpace ℂ A := fun x => Q x v with ha
  set T := toEuclideanCLM (𝕜 := ℂ) (((((2 : ℝ) ^ n)⁻¹ : ℂ)) • ∑ x, P x)
  have hTv : T v = ((N⁻¹ : ℝ) : ℂ) • ∑ x, a x := by
    simp only [T, map_smul, map_sum, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sum_apply, a, hQ, hN]
    push_cast; rfl
  have f1 : ∀ x, ‖a x‖ ^ 2 = (⟪v, a x⟫_ℂ).re := by
    intro x
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]
    have : ⟪a x, a x⟫_ℂ = ⟪v, a x⟫_ℂ := by simp only [ha]; rw [hsa, hid]
    rw [this]; rfl
  have f7 : ∀ x, ‖a x‖ ≤ ‖v‖ := by
    intro x
    have h1 := f1 x
    have h2 : (⟪v, a x⟫_ℂ).re ≤ ‖v‖ * ‖a x‖ := re_inner_le_norm (𝕜 := ℂ) v (a x)
    by_cases h0 : ‖a x‖ = 0
    · rw [h0]; exact norm_nonneg _
    · have hp : 0 < ‖a x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      nlinarith
  set S := ∑ x, ‖a x‖ ^ 2 with hS
  have f4 : S = N * (⟪v, T v⟫_ℂ).re := by
    rw [hTv, inner_smul_right, inner_sum]
    simp only [Complex.re_ofReal_mul, Complex.re_sum, hS, f1]
    field_simp
  have f4' : S ≤ N * (‖v‖ * ‖T v‖) := by
    rw [f4]; exact mul_le_mul_of_nonneg_left (re_inner_le_norm (𝕜 := ℂ) _ _) hNpos.le
  have f3 : N * ‖T v‖ ^ 2 =
      (∑ x, ∑ y, ((uniformLabelMatrix n x y : ℝ) : ℂ) * ⟪a x, a y⟫_ℂ).re := by
    have : (∑ x, ∑ y, ((uniformLabelMatrix n x y : ℝ) : ℂ) * ⟪a x, a y⟫_ℂ) =
        ((N⁻¹ : ℝ) : ℂ) * ⟪∑ x, a x, ∑ y, a y⟫_ℂ := by
      simp only [uniformLabelMatrix, sum_inner, inner_sum, Finset.mul_sum, hN]
      exact Finset.sum_comm
    rw [this, Complex.re_ofReal_mul, inner_self_eq_norm_sq_to_K, hTv, norm_smul]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hNpos]
    norm_cast
    field_simp
    exact (RCLike.ofReal_re (K := ℂ) _).symm
  have f5 : (∑ x, ∑ y, ((W x y : ℝ) : ℂ) * ⟪a x, a y⟫_ℂ).re ≤ ell * eta * S := by
    have term : ∀ x y, (((W x y : ℝ) : ℂ) * ⟪a x, a y⟫_ℂ).re ≤
        |W x y| * eta * (‖a x‖ * ‖a y‖) := by
      intro x y
      by_cases hw : W x y = 0
      · simp [hw]
      have hxy : ⟪a x, a y⟫_ℂ = ⟪a x, (Q x * Q y) (a y)⟫_ℂ := by
        show ⟪Q x v, Q y v⟫_ℂ = ⟪Q x v, Q x (Q y (Q y v))⟫_ℂ
        rw [hid y v, ← hsa x (Q x v), hid x v]
      have hnorm : ‖Q x * Q y‖ ≤ eta := by
        have := hoverlap x y hw
        simp only [hQ, ← map_mul]
        exact this
      calc (((W x y : ℝ) : ℂ) * ⟪a x, a y⟫_ℂ).re ≤ ‖((W x y : ℝ) : ℂ) * ⟪a x, a y⟫_ℂ‖ :=
            Complex.re_le_norm _
        _ = |W x y| * ‖⟪a x, (Q x * Q y) (a y)⟫_ℂ‖ := by
            rw [norm_mul, hxy, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ |W x y| * (‖a x‖ * (eta * ‖a y‖)) := by
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            refine (norm_inner_le_norm _ _).trans ?_
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
            exact ((Q x * Q y).le_opNorm _).trans
              (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _))
        _ = _ := by ring
    have amgm : ∀ x y, |W x y| * eta * (‖a x‖ * ‖a y‖) ≤
        eta * (|W x y| * ‖a x‖ ^ 2 / 2 + |W y x| * ‖a y‖ ^ 2 / 2) := by
      intro x y
      have hsym : W y x = W x y := by
        have := congrFun (congrFun hW x) y; simpa [Matrix.transpose_apply] using this
      rw [hsym]
      have : ‖a x‖ * ‖a y‖ ≤ ‖a x‖ ^ 2 / 2 + ‖a y‖ ^ 2 / 2 := by
        nlinarith [sq_nonneg (‖a x‖ - ‖a y‖)]
      have h0 : 0 ≤ |W x y| * eta := mul_nonneg (abs_nonneg _) he
      nlinarith
    rw [Complex.re_sum]
    calc ∑ x, (∑ y, ((W x y : ℝ) : ℂ) * ⟪a x, a y⟫_ℂ).re
        ≤ ∑ x, ∑ y, eta * (|W x y| * ‖a x‖ ^ 2 / 2 + |W y x| * ‖a y‖ ^ 2 / 2) := by
          apply Finset.sum_le_sum; intro x _
          rw [Complex.re_sum]
          apply Finset.sum_le_sum; intro y _
          exact (term x y).trans (amgm x y)
      _ = eta * ∑ x, (∑ y, |W x y|) * ‖a x‖ ^ 2 := by
          have hc : ∑ x, ∑ y, abs (W y x) * ‖a y‖ ^ 2 / 2 =
              ∑ x, ∑ y, abs (W x y) * ‖a x‖ ^ 2 / 2 := Finset.sum_comm
          simp only [← Finset.mul_sum]; congr 1
          simp only [Finset.sum_add_distrib]
          rw [hc, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro x _
          rw [← Finset.sum_add_distrib, Finset.sum_mul]
          apply Finset.sum_congr rfl; intro y _
          ring
      _ ≤ eta * ∑ x, ell * ‖a x‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ he
          exact Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_right (hrow x) (sq_nonneg _))
      _ = ell * eta * S := by rw [hS, ← Finset.mul_sum]; ring
  have f6 : (∑ x, ∑ y, (((uniformLabelMatrix n - W) x y : ℝ) : ℂ) * ⟪a x, a y⟫_ℂ).re ≤
      zeta * S := by
    refine (re_gram_le (uniformLabelMatrix n - W) a).trans ?_
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun x _ => sq_nonneg _))
    have : specNorm (W - uniformLabelMatrix n) =
        (@Norm.norm (Matrix _ _ ℝ) Matrix.instL2OpNormedAddCommGroup.toNorm
          (uniformLabelMatrix n - W)) := by
      unfold specNorm
      exact @norm_sub_rev (Matrix (Fin n → Bool) (Fin n → Bool) ℝ)
        Matrix.instL2OpNormedAddCommGroup.toSeminormedAddCommGroup.toSeminormedAddGroup _ _
    rw [← this]; exact happrox
  have hsplit : (∑ x, ∑ y, ((uniformLabelMatrix n x y : ℝ) : ℂ) * ⟪a x, a y⟫_ℂ) =
      (∑ x, ∑ y, ((W x y : ℝ) : ℂ) * ⟪a x, a y⟫_ℂ) +
      (∑ x, ∑ y, (((uniformLabelMatrix n - W) x y : ℝ) : ℂ) * ⟪a x, a y⟫_ℂ) := by
    simp only [← Finset.sum_add_distrib, Matrix.sub_apply]
    apply Finset.sum_congr rfl; intro x _; apply Finset.sum_congr rfl; intro y _
    push_cast; ring
  have key : N * ‖T v‖ ^ 2 ≤ (zeta + ell * eta) * (N * (‖v‖ * ‖T v‖)) := by
    rw [f3, hsplit, Complex.add_re]
    have hS0 : 0 ≤ S := Finset.sum_nonneg (fun x _ => sq_nonneg _)
    have hc : 0 ≤ zeta + ell * eta := by positivity
    nlinarith [mul_le_mul_of_nonneg_left f4' hc]
  have b1 : ‖T v‖ ≤ (zeta + ell * eta) * ‖v‖ := by
    by_cases h0 : ‖T v‖ = 0
    · rw [h0]; have : 0 ≤ zeta + ell * eta := by positivity
      exact mul_nonneg this (norm_nonneg _)
    · have hp : 0 < ‖T v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      have : N * ‖T v‖ * ‖T v‖ ≤ N * ((zeta + ell * eta) * ‖v‖) * ‖T v‖ := by nlinarith
      have := le_of_mul_le_mul_right this hp
      exact le_of_mul_le_mul_left this hNpos
  have b2 : ‖T v‖ ≤ ‖v‖ := by
    rw [hTv, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hNpos]
    calc N⁻¹ * ‖∑ x, a x‖ ≤ N⁻¹ * ∑ x, ‖a x‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
      _ ≤ N⁻¹ * ∑ _x : Fin n → Bool, ‖v‖ :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun x _ => f7 x)) (by positivity)
      _ = ‖v‖ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]; field_simp
  rcases le_total 1 (zeta + ell * eta) with h | h
  · rw [min_eq_left h, one_mul]; exact b2
  · rw [min_eq_right h]; exact b1


lemma min_le {zeta ell eta : ℝ} (hz : 0 ≤ zeta) (hl : 0 ≤ ell) (he : 0 ≤ eta) :
    min 1 (zeta + ell * eta) ≤ zeta + Real.sqrt (ell * eta) := by
  have h0 : 0 ≤ ell * eta := mul_nonneg hl he
  rcases le_total (ell * eta) 1 with h | h
  · have : ell * eta ≤ Real.sqrt (ell * eta) := by
      rw [Real.le_sqrt h0 h0]; nlinarith
    exact (min_le_right _ _).trans (by linarith)
  · have : 1 ≤ Real.sqrt (ell * eta) := by
      rw [Real.le_sqrt zero_le_one h0]; linarith
    exact (min_le_left _ _).trans (by linarith)

end X7AP

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

open MeasureTheory Filter

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P67 in
theorem solution {A : Type*} [Fintype A] [DecidableEq A] {n : ℕ} [Nonempty A]
    (P : (Fin n → Bool) → Matrix A A ℂ)
    (hP : ∀ x, (P x)ᴴ = P x ∧ P x * P x = P x)
    (W : Matrix (Fin n → Bool) (Fin n → Bool) ℝ) (hW : W.transpose = W)
    (zeta ell eta : ℝ) (hz : 0 ≤ zeta) (hl : 0 ≤ ell) (he : 0 ≤ eta)
    (happrox : specNorm (W - uniformLabelMatrix n) ≤ zeta)
    (hrow : ∀ x, ∑ y, |W x y| ≤ ell)
    (hoverlap : ∀ x y, W x y ≠ 0 → specNorm (P x * P y) ≤ eta) :
    specNorm (((((2 : ℝ) ^ n)⁻¹ : ℂ)) • ∑ x, P x) ≤ zeta + Real.sqrt (ell * eta) := by
  unfold specNorm
  rw [Matrix.cstar_norm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun v => ?_)
  refine (X7AP.main_bound P hP W hW zeta ell eta hz hl he happrox hrow hoverlap v).trans ?_
  exact mul_le_mul_of_nonneg_right (X7AP.min_le hz hl he) (norm_nonneg _)

-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P38.operatorBlockMatrixNormComparison
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T17:16:44.740841+00:00
-- url     : https://prove2.me/submissions/674fe140-a85e-4792-a68b-3f0bcf82b904

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P38
noncomputable section

open scoped BigOperators InnerProductSpace

namespace G62B

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem sa_inner {e : H →L[ℂ] H} (he : IsSelfAdjoint e) (a b : H) : ⟪e a, b⟫_ℂ = ⟪a, e b⟫_ℂ := by
  have h : ContinuousLinearMap.adjoint e = e := by
    rw [← ContinuousLinearMap.star_eq_adjoint]; exact he
  rw [← ContinuousLinearMap.adjoint_inner_left, h]

theorem bessel {I : Type*} [Fintype I] (e : I → (H →L[ℂ] H)) (he : ∀ i, IsStarProjection (e i))
    (hd : Pairwise (fun i k => e i * e k = 0)) (η : H) :
    ∑ i, ‖e i η‖ ^ 2 ≤ ‖η‖ ^ 2 := by
  classical
  set s := ∑ i, ‖e i η‖ ^ 2 with hs
  have hi : ∀ i k, ⟪e i η, e k η⟫_ℂ = if i = k then ⟪e i η, η⟫_ℂ else 0 := by
    intro i k
    rw [sa_inner (he i).isSelfAdjoint, ← ContinuousLinearMap.mul_apply]
    split_ifs with h
    · subst h; rw [(he i).isIdempotentElem.eq, ← sa_inner (he i).isSelfAdjoint]
    · rw [hd h]; simp
  have hn : ∀ v : H, ‖v‖ ^ 2 = (⟪v, v⟫_ℂ).re := fun v => by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]; rfl
  have h1 : s = (⟪∑ i, e i η, η⟫_ℂ).re := by
    rw [hs, sum_inner, Complex.re_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hn, hi i i, if_pos rfl]
  have h2 : ‖∑ i, e i η‖ ^ 2 = s := by
    rw [hn, sum_inner, h1, sum_inner]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [inner_sum]
    simp_rw [hi i]
    rw [Finset.sum_ite_eq]
    simp
  have h3 : s ≤ ‖∑ i, e i η‖ * ‖η‖ := by
    rw [h1]; exact re_inner_le_norm (𝕜 := ℂ) _ _
  have ht := norm_nonneg (∑ i, e i η)
  have hη := norm_nonneg η
  nlinarith


theorem fin_bound {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (A : Matrix (I ⊕ J) (I ⊕ J) ℂ) (a : I → J → ℝ) (ha : ∀ i j, A (Sum.inl i) (Sum.inr j) = a i j)
    (u : I → ℝ) (v : J → ℝ) :
    ∑ i, ∑ j, a i j * u i * v j ≤
      ‖Matrix.toEuclideanCLM (n := I ⊕ J) (𝕜 := ℂ) A‖ * Real.sqrt (∑ i, u i ^ 2) *
        Real.sqrt (∑ j, v j ^ 2) := by
  set T := Matrix.toEuclideanCLM (n := I ⊕ J) (𝕜 := ℂ) A
  let U : EuclideanSpace ℂ (I ⊕ J) := WithLp.toLp 2 (Sum.elim (fun i => (u i : ℂ)) 0)
  let V : EuclideanSpace ℂ (I ⊕ J) := WithLp.toLp 2 (Sum.elim 0 (fun j => (v j : ℂ)))
  have hin : ⟪U, T V⟫_ℂ = ((∑ i, ∑ j, a i j * u i * v j : ℝ) : ℂ) := by
    simp only [T, U, V, Matrix.toEuclideanCLM_toLp, EuclideanSpace.inner_toLp_toLp, dotProduct,
      Matrix.mulVec, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, mul_zero,
      zero_mul, Finset.sum_const_zero, zero_add, add_zero, Pi.star_apply, ha]
    push_cast
    simp only [star_zero, mul_zero, Finset.sum_const_zero, add_zero, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [Complex.star_def, Complex.conj_ofReal]
    ring
  have hU : ‖U‖ = Real.sqrt (∑ i, u i ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    simp [U, Fintype.sum_sum_type]
  have hV : ‖V‖ = Real.sqrt (∑ j, v j ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    simp [V, Fintype.sum_sum_type]
  have h1 : (∑ i, ∑ j, a i j * u i * v j) = (⟪U, T V⟫_ℂ).re := by rw [hin, Complex.ofReal_re]
  rw [h1]
  calc (⟪U, T V⟫_ℂ).re ≤ ‖U‖ * ‖T V‖ := re_inner_le_norm (𝕜 := ℂ) _ _
    _ ≤ ‖U‖ * (‖T‖ * ‖V‖) := by gcongr; exact T.le_opNorm V
    _ = _ := by rw [hU, hV]; ring

end G62B

open QAlgorithms.Papers.Independent.Next46.P38

universe u v w

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem solution
    {I : Type v} {J : Type w} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (x : I → J → (H →L[ℂ] H))
    (e : I → (H →L[ℂ] H)) (f : J → (H →L[ℂ] H))
    (he : ∀ i, IsStarProjection (e i))
    (hf : ∀ j, IsStarProjection (f j))
    (heDisjoint : Pairwise (fun i k => e i * e k = 0))
    (hfDisjoint : Pairwise (fun j k => f j * f k = 0)) :
    ‖∑ i : I, ∑ j : J, e i * x i j * f j‖ ≤
      ‖Matrix.toEuclideanCLM (n := Sum I J) (𝕜 := ℂ) (blockNormPadding x e f)‖ := by
  set T := Matrix.toEuclideanCLM (n := Sum I J) (𝕜 := ℂ) (blockNormPadding x e f)
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun ξ => ?_)
  set η := (∑ i : I, ∑ j : J, e i * x i j * f j) ξ with hη
  have hterm : ∀ i j, ‖⟪η, (e i * x i j * f j) ξ⟫_ℂ‖ ≤ ‖e i * x i j * f j‖ * ‖e i η‖ * ‖f j ξ‖ := by
    intro i j
    have h1 : (e i * x i j * f j) ξ = e i ((e i * x i j * f j) (f j ξ)) := by
      have hf2 : f j (f j ξ) = f j ξ := by
        have := congrArg (fun M : H →L[ℂ] H => M ξ) (hf j).isIdempotentElem.eq
        simpa using this
      have he2 : ∀ w, e i (e i w) = e i w := fun w => by
        have := congrArg (fun M : H →L[ℂ] H => M w) (he i).isIdempotentElem.eq
        simpa using this
      simp only [ContinuousLinearMap.mul_apply, hf2, he2]
    rw [h1, ← G62B.sa_inner (he i).isSelfAdjoint]
    calc ‖⟪e i η, (e i * x i j * f j) (f j ξ)⟫_ℂ‖ ≤ ‖e i η‖ * ‖(e i * x i j * f j) (f j ξ)‖ :=
          norm_inner_le_norm _ _
      _ ≤ ‖e i η‖ * (‖e i * x i j * f j‖ * ‖f j ξ‖) := by
          gcongr; exact ContinuousLinearMap.le_opNorm _ _
      _ = _ := by ring
  have hsq : ‖η‖ ^ 2 ≤ ∑ i, ∑ j, ‖e i * x i j * f j‖ * ‖e i η‖ * ‖f j ξ‖ := by
    have : ‖η‖ ^ 2 = (⟪η, η⟫_ℂ).re := by rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]; rfl
    have hexp : ⟪η, η⟫_ℂ = ∑ i, ∑ j, ⟪η, (e i * x i j * f j) ξ⟫_ℂ := by
      calc ⟪η, η⟫_ℂ = ⟪η, (∑ i : I, ∑ j : J, e i * x i j * f j) ξ⟫_ℂ := rfl
        _ = _ := by
          rw [ContinuousLinearMap.sum_apply, inner_sum]
          simp_rw [ContinuousLinearMap.sum_apply, inner_sum]
    rw [this, hexp, Complex.re_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    rw [Complex.re_sum]
    refine Finset.sum_le_sum (fun j _ => ?_)
    exact (Complex.re_le_norm _).trans (hterm i j)
  have hfin := G62B.fin_bound (blockNormPadding x e f) (fun i j => ‖e i * x i j * f j‖)
    (fun i j => rfl) (fun i => ‖e i η‖) (fun j => ‖f j ξ‖)
  have hb1 := G62B.bessel e he heDisjoint η
  have hb2 := G62B.bessel f hf hfDisjoint ξ
  have hs1 : Real.sqrt (∑ i, ‖e i η‖ ^ 2) ≤ ‖η‖ :=
    Real.sqrt_le_iff.2 ⟨norm_nonneg _, hb1⟩
  have hs2 : Real.sqrt (∑ j, ‖f j ξ‖ ^ 2) ≤ ‖ξ‖ :=
    Real.sqrt_le_iff.2 ⟨norm_nonneg _, hb2⟩
  have hT := norm_nonneg T
  have key : ‖η‖ ^ 2 ≤ ‖T‖ * ‖η‖ * ‖ξ‖ := by
    calc ‖η‖ ^ 2 ≤ _ := hsq
      _ ≤ _ := hfin
      _ ≤ ‖T‖ * ‖η‖ * ‖ξ‖ := by
        gcongr
  have hη0 := norm_nonneg η
  have hξ0 := norm_nonneg ξ
  rcases hη0.eq_or_lt with h0 | hpos
  · rw [← h0]; positivity
  · nlinarith

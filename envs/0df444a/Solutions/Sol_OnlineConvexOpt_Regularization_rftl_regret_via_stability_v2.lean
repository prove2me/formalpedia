-- Prove2me | solution 1 for OnlineConvexOpt.Regularization.rftl_regret_via_stability_v2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T19:26:20.745698+00:00
-- url     : https://prove2.me/submissions/561345d1-3d00-4c0d-9589-2e43085f1162

import Mathlib
import Definitions.Def_OnlineConvexOpt_Regularization_Protocol_v2
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol_v2

open scoped InnerProductSpace
open OnlineConvexOpt.Regularization OnlineConvexOpt.FirstOrder


namespace OnlineConvexOpt.Regularization

lemma rftlv2_grad_ineq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (K : Set E) (f : E → ℝ) (hfconv : ConvexOn ℝ K f) (gx x y : E) (hx : x ∈ K) (hy : y ∈ K)
    (hg : HasGradientAt f gx x) : f x + ⟪gx, y - x⟫_ℝ ≤ f y := by
  set L : ℝ →ᵃ[ℝ] E := AffineMap.lineMap x y with hL
  have e : ∀ s : ℝ, L s = x + s • (y - x) := by
    intro s; rw [hL, AffineMap.lineMap_apply_module']; abel
  have hc : ConvexOn ℝ (L ⁻¹' K) (fun s : ℝ => f (x + s • (y - x))) := by
    have h := hfconv.comp_affineMap L
    have heq : (f ∘ L) = fun s : ℝ => f (x + s • (y - x)) := by funext s; simp [e]
    rw [heq] at h; exact h
  have hd : HasDerivAt (fun s : ℝ => x + s • (y - x)) (y - x) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (y - x)).const_add x
  have hd2 : HasDerivAt (fun s : ℝ => f (x + s • (y - x))) ⟪gx, y - x⟫_ℝ 0 := by
    have h1 := hg.hasFDerivAt
    have h1' : HasFDerivAt f ((InnerProductSpace.toDual ℝ E) gx) (x + (0:ℝ) • (y - x)) := by
      simpa using h1
    have := h1'.comp_hasDerivAt (0:ℝ) hd
    rw [InnerProductSpace.toDual_apply_apply] at this
    exact this
  have h0 : (0:ℝ) ∈ L ⁻¹' K := by simp [e, hx]
  have h1 : (1:ℝ) ∈ L ⁻¹' K := by simp [e, hy]
  have := hc.le_slope_of_hasDerivAt h0 h1 zero_lt_one hd2
  simp [slope] at this
  linarith

/-- first-order optimality for `y ↦ η Σ ⟪g s, y⟫ + R y` -/
lemma rftlv2_first_order {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (K : Set E) (hKconv : Convex ℝ K) (R : E → ℝ) (η : ℝ) (g : ℕ → E) (n : ℕ) (p r : E)
    (hp : IsArgMinOn (fun y => η * (∑ s ∈ Finset.range n, ⟪g s, y⟫_ℝ) + R y) K p)
    (hr : HasGradientAt R r p) (y : E) (hy : y ∈ K) :
    0 ≤ η * (∑ s ∈ Finset.range n, ⟪g s, y - p⟫_ℝ) + ⟪r, y - p⟫_ℝ := by
  set d := y - p with hd
  have hdR : HasDerivAt (fun s : ℝ => R (p + s • d)) ⟪r, d⟫_ℝ 0 := by
    have hl : HasDerivAt (fun s : ℝ => p + s • d) d 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).smul_const d).const_add p
    have h1' : HasFDerivAt R ((InnerProductSpace.toDual ℝ E) r) (p + (0:ℝ) • d) := by
      simpa using hr.hasFDerivAt
    have := h1'.comp_hasDerivAt (0:ℝ) hl
    rw [InnerProductSpace.toDual_apply_apply] at this
    exact this
  have hlin : HasDerivAt (fun s : ℝ => η * (∑ i ∈ Finset.range n, ⟪g i, p⟫_ℝ)
      + s * (η * ∑ i ∈ Finset.range n, ⟪g i, d⟫_ℝ))
      (η * ∑ i ∈ Finset.range n, ⟪g i, d⟫_ℝ) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const (η * ∑ i ∈ Finset.range n, ⟪g i, d⟫_ℝ)).const_add
      (η * (∑ i ∈ Finset.range n, ⟪g i, p⟫_ℝ))
  have hφ := hlin.add hdR
  set φ : ℝ → ℝ := fun s => (η * (∑ i ∈ Finset.range n, ⟪g i, p⟫_ℝ)
      + s * (η * ∑ i ∈ Finset.range n, ⟪g i, d⟫_ℝ)) + R (p + s • d) with hφdef
  have hφeq : ∀ s : ℝ, φ s = η * (∑ i ∈ Finset.range n, ⟪g i, p + s • d⟫_ℝ) + R (p + s • d) := by
    intro s
    simp only [hφdef, inner_add_right, inner_smul_right, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    ring
  have hmin : IsMinOn φ (Set.Icc (0:ℝ) 1) 0 := by
    intro s hs
    show φ 0 ≤ φ s
    rw [hφeq, hφeq]
    simp only [zero_smul, add_zero]
    apply hp.2
    have : p + s • d = (1 - s) • p + s • y := by
      rw [hd, smul_sub, sub_smul, one_smul]; abel
    rw [this]
    exact hKconv hp.1 hy (by linarith [hs.2]) hs.1 (by ring)
  have hloc : IsLocalMinOn φ (Set.Icc (0:ℝ) 1) 0 := hmin.localize
  have hmem : (1:ℝ) ∈ posTangentConeAt (Set.Icc (0:ℝ) 1) 0 := by
    apply mem_posTangentConeAt_of_segment_subset
    rw [segment_eq_Icc (by norm_num)]
    simp
  have := hloc.hasFDerivWithinAt_nonneg hφ.hasFDerivAt.hasFDerivWithinAt hmem
  simpa [Finset.mul_sum] using this

lemma rftlv2_mem {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (K : Set E) (R : E → ℝ) (η : ℝ) (f : ℕ → E → ℝ) (x grad : ℕ → E)
    (hRun : IsRFTLRun K R η f x grad) (t : ℕ) : x t ∈ K := by
  cases t with
  | zero => exact hRun.1.1
  | succ t => exact (hRun.2.2 t).1

lemma rftlv2_min {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (K : Set E) (R : E → ℝ) (η : ℝ) (f : ℕ → E → ℝ) (x grad : ℕ → E)
    (hRun : IsRFTLRun K R η f x grad) (t : ℕ) :
    IsArgMinOn (fun y => η * (∑ s ∈ Finset.range t, ⟪grad s, y⟫_ℝ) + R y) K (x t) := by
  cases t with
  | zero =>
    refine ⟨hRun.1.1, fun y hy => ?_⟩
    simpa using hRun.1.2 y hy
  | succ t => exact hRun.2.2 t

/-- be-the-leader -/
lemma rftlv2_btl {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (K : Set E) (R : E → ℝ) (η : ℝ) (f : ℕ → E → ℝ) (x grad : ℕ → E)
    (hRun : IsRFTLRun K R η f x grad) (T : ℕ) : ∀ u ∈ K,
    η * (∑ t ∈ Finset.range T, ⟪grad t, x (t + 1)⟫_ℝ) + R (x 0) ≤
      η * (∑ t ∈ Finset.range T, ⟪grad t, u⟫_ℝ) + R u := by
  induction T with
  | zero => intro u hu; simpa using hRun.1.2 u hu
  | succ T ih =>
    intro u hu
    have h1 := ih (x (T + 1)) (hRun.2.2 T).1
    have h2 := (hRun.2.2 T).2 u hu
    simp only at h2
    rw [Finset.sum_range_succ (fun t => ⟪grad t, x (T + 1)⟫_ℝ),
      Finset.sum_range_succ (fun t => ⟪grad t, u⟫_ℝ)] at h2
    rw [Finset.sum_range_succ (fun t => ⟪grad t, x (t + 1)⟫_ℝ),
      Finset.sum_range_succ (fun t => ⟪grad t, u⟫_ℝ)]
    nlinarith

lemma rftlv2_linear {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (K : Set E) (R : E → ℝ) (η : ℝ) (hη : 0 < η) (f : ℕ → E → ℝ)
    (hfconv : ∀ t, ConvexOn ℝ K (f t)) (x grad : ℕ → E) (hRun : IsRFTLRun K R η f x grad)
    (T : ℕ) (u : E) (hu : u ∈ K) :
    (∑ t ∈ Finset.range T, (f t (x t) - f t u)) ≤
      (∑ t ∈ Finset.range T, ⟪grad t, x t - x (t + 1)⟫_ℝ) + (R u - R (x 0)) / η := by
  have h1 : (∑ t ∈ Finset.range T, (f t (x t) - f t u)) ≤
      ∑ t ∈ Finset.range T, ⟪grad t, x t - u⟫_ℝ := by
    apply Finset.sum_le_sum
    intro t _
    have := rftlv2_grad_ineq K (f t) (hfconv t) (grad t) (x t) u
      (rftlv2_mem K R η f x grad hRun t) hu (hRun.2.1 t)
    rw [show x t - u = -(u - x t) by abel, inner_neg_right]
    linarith
  have h2 := rftlv2_btl K R η f x grad hRun T u hu
  have e1 : ∑ t ∈ Finset.range T, ⟪grad t, x t - u⟫_ℝ =
      ∑ t ∈ Finset.range T, ⟪grad t, x t - x (t + 1)⟫_ℝ +
      (∑ t ∈ Finset.range T, ⟪grad t, x (t + 1)⟫_ℝ - ∑ t ∈ Finset.range T, ⟪grad t, u⟫_ℝ) := by
    simp only [inner_sub_right, Finset.sum_sub_distrib]; ring
  have h3 : (∑ t ∈ Finset.range T, ⟪grad t, x (t + 1)⟫_ℝ - ∑ t ∈ Finset.range T, ⟪grad t, u⟫_ℝ)
      ≤ (R u - R (x 0)) / η := by
    rw [le_div_iff₀ hη]; nlinarith
  linarith

theorem rftl_regret_via_stability_v2_core {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (K : Set E) (hKconv : Convex ℝ K) (hKne : K.Nonempty) (hKbdd : Bornology.IsBounded K)
    (R : E → ℝ) (gradR : E → E) (η : ℝ) (hη : 0 < η)
    (f : ℕ → E → ℝ) (hfconv : ∀ t, ConvexOn ℝ K (f t))
    (x grad : ℕ → E) (hRun : IsRFTLRun K R η f x grad)
    (hRbdd : BddAbove (Set.image2 (fun p q => R p - R q) K K)) (T : ℕ) :
    RegretT K f x T ≤
      (∑ t ∈ Finset.range T, ⟪grad t, x t - x (t + 1)⟫_ℝ) + (1 / η) * RDiameterSq R K := by
  unfold RegretT
  have hne : ((fun y => ∑ t ∈ Finset.range T, f t y) '' K).Nonempty := hKne.image _
  have : (∑ t ∈ Finset.range T, f t (x t)) -
      ((∑ t ∈ Finset.range T, ⟪grad t, x t - x (t + 1)⟫_ℝ) + (1 / η) * RDiameterSq R K) ≤
      sInf ((fun y => ∑ t ∈ Finset.range T, f t y) '' K) := by
    apply le_csInf hne
    rintro _ ⟨u, hu, rfl⟩
    have h := rftlv2_linear K R η hη f hfconv x grad hRun T u hu
    have hD : R u - R (x 0) ≤ RDiameterSq R K :=
      le_csSup hRbdd ⟨u, hu, x 0, hRun.1.1, rfl⟩
    have hdiv : (R u - R (x 0)) / η ≤ (1 / η) * RDiameterSq R K := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_left hD (by positivity)
    rw [Finset.sum_sub_distrib] at h
    simp only
    linarith
  linarith

end OnlineConvexOpt.Regularization

open OnlineConvexOpt.Regularization


theorem solution
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (K : Set E) (hKconv : Convex ℝ K) (hKne : K.Nonempty) (hKbdd : Bornology.IsBounded K)
    (R : E → ℝ) (gradR : E → E) (η : ℝ) (hη : 0 < η)
    (f : ℕ → E → ℝ) (hfconv : ∀ t, ConvexOn ℝ K (f t))
    (x grad : ℕ → E) (hRun : IsRFTLRun K R η f x grad)
    (hRbdd : BddAbove (Set.image2 (fun p q => R p - R q) K K)) (T : ℕ) :
    RegretT K f x T ≤
      (∑ t ∈ Finset.range T, ⟪grad t, x t - x (t + 1)⟫_ℝ) + (1 / η) * RDiameterSq R K := by
  exact rftl_regret_via_stability_v2_core K hKconv hKne hKbdd R gradR η hη f hfconv x grad hRun hRbdd T

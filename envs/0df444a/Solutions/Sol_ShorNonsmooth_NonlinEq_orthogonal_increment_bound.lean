-- Prove2me | solution 1 for ShorNonsmooth.NonlinEq.orthogonal_increment_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T09:30:11.784167+00:00
-- url     : https://prove2.me/submissions/6659e415-7c41-44c8-9c79-ffe600115b62

import Mathlib
set_option autoImplicit false

theorem solution {n : ℕ} (ψ : Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (hψ : ∀ i, ContDiff ℝ 1 (ψ i)) (δ L : ℝ) (hδ : 0 < δ)
    (hLip : ∀ i, ∀ x' ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ,
      ∀ x'' ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ,
        ‖gradient (ψ i) x' - gradient (ψ i) x''‖ ≤ L * ‖x' - x''‖)
    (i : Fin n) (x₁ x₂ ξ : EuclideanSpace ℝ (Fin n)) (hξ : ‖ξ‖ = 1)
    (horth : inner ℝ (gradient (ψ i) x₁) ξ = 0) (h : ℝ) (hh : 0 < h)
    (hx₁ : x₁ ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ)
    (hx₂ : x₂ ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ)
    (hx₂h : x₂ + h • ξ ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ) :
    |ψ i (x₂ + h • ξ) - ψ i x₂| ≤ L * h * (h + ‖x₁ - x₂‖) := by
  have hconv := convex_ball (0 : EuclideanSpace ℝ (Fin n)) δ
  -- points on the segment lie in the ball
  have hseg : ∀ t ∈ Set.Icc (0:ℝ) h, x₂ + t • ξ ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ := by
    intro t ht
    have : x₂ + t • ξ = (1 - t / h) • x₂ + (t / h) • (x₂ + h • ξ) := by
      have hne : h ≠ 0 := hh.ne'
      rw [smul_add, smul_smul, div_mul_cancel₀ _ hne, sub_smul, one_smul]
      abel
    rw [this]
    refine hconv hx₂ hx₂h (by rw [sub_nonneg, div_le_one hh]; exact ht.2) (div_nonneg ht.1 hh.le) (by ring)
  -- L ≥ 0
  have hL : 0 ≤ L := by
    have := hLip i x₂ hx₂ _ hx₂h
    have h2 : ‖x₂ - (x₂ + h • ξ)‖ = h := by
      rw [sub_add_cancel_left, norm_neg, norm_smul, hξ, Real.norm_of_nonneg hh.le, mul_one]
    rw [h2] at this
    nlinarith [norm_nonneg (gradient (ψ i) x₂ - gradient (ψ i) (x₂ + h • ξ))]
  set φ : ℝ → ℝ := fun t => ψ i (x₂ + t • ξ) with hφ
  have hgr : ∀ p, inner ℝ (gradient (ψ i) p) ξ = fderiv ℝ (ψ i) p ξ := by
    intro p
    simp [gradient, InnerProductSpace.toDual_symm_apply]
  have hderiv : ∀ t : ℝ, HasDerivAt φ (inner ℝ (gradient (ψ i) (x₂ + t • ξ)) ξ) t := by
    intro t
    have h1 : HasFDerivAt (ψ i) (fderiv ℝ (ψ i) (x₂ + t • ξ)) (x₂ + t • ξ) :=
      ((hψ i).differentiable one_ne_zero _).hasFDerivAt
    have h2 : HasDerivAt (fun t : ℝ => x₂ + t • ξ) ξ t := by
      simpa using ((hasDerivAt_id t).smul_const ξ).const_add x₂
    rw [hgr]
    exact h1.comp_hasDerivAt t h2
  have hbound : ∀ t ∈ Set.Icc (0:ℝ) h,
      ‖inner ℝ (gradient (ψ i) (x₂ + t • ξ)) ξ‖ ≤ L * (‖x₁ - x₂‖ + h) := by
    intro t ht
    have hp := hseg t ht
    have h1 := hLip i _ hp x₁ hx₁
    have h2 : inner ℝ (gradient (ψ i) (x₂ + t • ξ)) ξ
        = inner ℝ (gradient (ψ i) (x₂ + t • ξ) - gradient (ψ i) x₁) ξ := by
      rw [inner_sub_left, horth, sub_zero]
    rw [h2]
    refine (norm_inner_le_norm _ _).trans ?_
    rw [hξ, mul_one]
    refine h1.trans ?_
    have h3 : ‖x₂ + t • ξ - x₁‖ ≤ ‖x₁ - x₂‖ + h := by
      have : x₂ + t • ξ - x₁ = -(x₁ - x₂) + t • ξ := by abel
      rw [this]
      refine (norm_add_le _ _).trans ?_
      rw [norm_neg, norm_smul, hξ, Real.norm_of_nonneg ht.1, mul_one]
      linarith [ht.2]
    exact mul_le_mul_of_nonneg_left h3 hL
  have key := (convex_Icc (0:ℝ) h).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := φ) (f' := fun t => inner ℝ (gradient (ψ i) (x₂ + t • ξ)) ξ)
    (fun t _ => (hderiv t).hasDerivWithinAt) hbound
    (Set.left_mem_Icc.2 hh.le) (Set.right_mem_Icc.2 hh.le)
  simp only [hφ, zero_smul, add_zero, Real.norm_eq_abs, sub_zero, abs_of_pos hh] at key
  calc |ψ i (x₂ + h • ξ) - ψ i x₂| ≤ L * (‖x₁ - x₂‖ + h) * h := key
    _ = L * h * (h + ‖x₁ - x₂‖) := by ring

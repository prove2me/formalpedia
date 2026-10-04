-- Prove2me | solution 1 for ShorNonsmooth.Decomposition.subgradient_formula_differentiable
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T06:03:14.399081+00:00
-- url     : https://prove2.me/submissions/065133da-134e-4d7f-a455-5249ea9f99a5

import Mathlib
import Definitions.Def_ShorNonsmooth_Decomposition_ValueFunction

set_option autoImplicit false

open ShorNonsmooth.Decomposition in
theorem p52e8c78a_valueFn_eq {l m n : ℕ}
    (f₀ : EuclideanSpace ℝ (Fin l) → EuclideanSpace ℝ (Fin m) → ℝ)
    (f : Fin n → EuclideanSpace ℝ (Fin l) → EuclideanSpace ℝ (Fin m) → ℝ)
    (x : EuclideanSpace ℝ (Fin l)) (y : EuclideanSpace ℝ (Fin m))
    (hy : IsOptimalY f₀ f x y) : valueFn f₀ f x = f₀ x y := by
  unfold valueFn
  apply IsLeast.csInf_eq
  refine ⟨⟨y, hy.1, rfl⟩, ?_⟩
  rintro _ ⟨y', hy', rfl⟩
  exact hy.2 y' hy'

-- The weighted sum of joint subgradients is a joint subgradient of the Lagrangian.
open ShorNonsmooth.Decomposition in
theorem p52e8c78a_lag_subgrad {l m n : ℕ}
    (f₀ : EuclideanSpace ℝ (Fin l) → EuclideanSpace ℝ (Fin m) → ℝ)
    (f : Fin n → EuclideanSpace ℝ (Fin l) → EuclideanSpace ℝ (Fin m) → ℝ)
    (xbar : EuclideanSpace ℝ (Fin l)) (ybar : EuclideanSpace ℝ (Fin m))
    (U : Fin n → ℝ) (hU : ∀ i, 0 ≤ U i)
    (gx₀ : EuclideanSpace ℝ (Fin l)) (gy₀ : EuclideanSpace ℝ (Fin m))
    (hg₀ : IsJointSubgradient f₀ xbar ybar gx₀ gy₀)
    (gx : Fin n → EuclideanSpace ℝ (Fin l)) (gy : Fin n → EuclideanSpace ℝ (Fin m))
    (hg : ∀ i, IsJointSubgradient (f i) xbar ybar (gx i) (gy i)) :
    IsJointSubgradient (lagrangian f₀ f U) xbar ybar (gx₀ + ∑ i, U i • gx i)
      (gy₀ + ∑ i, U i • gy i) := by
  intro x y
  have e : lagrangian f₀ f U x y - lagrangian f₀ f U xbar ybar
      = (f₀ x y - f₀ xbar ybar) + ∑ i, U i * (f i x y - f i xbar ybar) := by
    unfold lagrangian
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  have ex : inner ℝ (gx₀ + ∑ i, U i • gx i) (x - xbar)
      = inner ℝ gx₀ (x - xbar) + ∑ i, U i * inner ℝ (gx i) (x - xbar) := by
    rw [inner_add_left, sum_inner]
    simp only [real_inner_smul_left]
  have ey : inner ℝ (gy₀ + ∑ i, U i • gy i) (y - ybar)
      = inner ℝ gy₀ (y - ybar) + ∑ i, U i * inner ℝ (gy i) (y - ybar) := by
    rw [inner_add_left, sum_inner]
    simp only [real_inner_smul_left]
  rw [e, ex, ey]
  have h0 := hg₀ x y
  have hs : ∑ i, U i * (inner ℝ (gx i) (x - xbar) + inner ℝ (gy i) (y - ybar))
      ≤ ∑ i, U i * (f i x y - f i xbar ybar) :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hg i x y) (hU i)
  have hs' : ∑ i, U i * (inner ℝ (gx i) (x - xbar) + inner ℝ (gy i) (y - ybar))
      = ∑ i, U i * inner ℝ (gx i) (x - xbar) + ∑ i, U i * inner ℝ (gy i) (y - ybar) := by
    rw [← Finset.sum_add_distrib]
    simp only [mul_add]
  rw [hs'] at hs
  have h0' : f₀ x y - f₀ xbar ybar ≥ inner ℝ gx₀ (x - xbar) + inner ℝ gy₀ (y - ybar) := h0
  linarith

-- A subgradient (in y) of a function differentiable at a minimizer is zero.
theorem p52e8c78a_subgrad_zero {m : ℕ}
    (φ : EuclideanSpace ℝ (Fin m) → ℝ) (ybar H : EuclideanSpace ℝ (Fin m))
    (hφ : DifferentiableAt ℝ φ ybar) (hmin : ∀ y, φ ybar ≤ φ y)
    (hsub : ∀ y, φ y - φ ybar ≥ inner ℝ H (y - ybar)) : H = 0 := by
  have hD : HasFDerivAt φ (fderiv ℝ φ ybar) ybar := hφ.hasFDerivAt
  have h1 : fderiv ℝ φ ybar = 0 :=
    IsLocalMin.hasFDerivAt_eq_zero (Filter.Eventually.of_forall hmin) hD
  set ψ : EuclideanSpace ℝ (Fin m) → ℝ := fun y => φ y - innerSL ℝ H y with hψ
  have hψD : HasFDerivAt ψ (fderiv ℝ φ ybar - innerSL ℝ H) ybar :=
    hD.sub (innerSL ℝ H).hasFDerivAt
  have hψmin : IsLocalMin ψ ybar := by
    refine Filter.Eventually.of_forall fun y => ?_
    have := hsub y
    simp only [hψ, innerSL_apply_apply, inner_sub_right] at this ⊢
    linarith
  have h2 := hψmin.hasFDerivAt_eq_zero hψD
  rw [h1, zero_sub, neg_eq_zero] at h2
  have h3 : innerSL ℝ H H = 0 := by rw [h2]; rfl
  rw [innerSL_apply_apply] at h3
  exact inner_self_eq_zero.mp h3

open ShorNonsmooth.Decomposition in
theorem solution {l m n : ℕ}
    (f₀ : EuclideanSpace ℝ (Fin l) → EuclideanSpace ℝ (Fin m) → ℝ)
    (f : Fin n → EuclideanSpace ℝ (Fin l) → EuclideanSpace ℝ (Fin m) → ℝ)
    (hf₀ : JointlyConvex f₀) (hf : ∀ i, JointlyConvex (f i))
    (hd₀ : ∀ x, ContDiff ℝ 1 (f₀ x)) (hd : ∀ i x, ContDiff ℝ 1 (f i x))
    (W : Set (EuclideanSpace ℝ (Fin l))) (hW : Convex ℝ W)
    (hWmin : ∀ x ∈ W, MinAttained f₀ f x)
    (xbar : EuclideanSpace ℝ (Fin l)) (hxbar : xbar ∈ W) (hslater : SlaterAt f xbar)
    (ybar : EuclideanSpace ℝ (Fin m)) (hybar : IsOptimalY f₀ f xbar ybar)
    (U : Fin n → ℝ) (hU : IsKuhnTuckerMultiplier f₀ f xbar ybar U)
    (gx₀ : EuclideanSpace ℝ (Fin l)) (gy₀ : EuclideanSpace ℝ (Fin m))
    (hg₀ : IsJointSubgradient f₀ xbar ybar gx₀ gy₀)
    (gx : Fin n → EuclideanSpace ℝ (Fin l)) (gy : Fin n → EuclideanSpace ℝ (Fin m))
    (hg : ∀ i, IsJointSubgradient (f i) xbar ybar (gx i) (gy i)) :
    IsSubgradientOn (valueFn f₀ f) W xbar (gx₀ + ∑ i, U i • gx i) := by
  have hJ := p52e8c78a_lag_subgrad f₀ f xbar ybar U hU.1 gx₀ gy₀ hg₀ gx gy hg
  have hdiff : DifferentiableAt ℝ (fun y => lagrangian f₀ f U xbar y) ybar := by
    have h0 : DifferentiableAt ℝ (f₀ xbar) ybar :=
      ((hd₀ xbar).differentiable one_ne_zero) ybar
    have hi : ∀ i, DifferentiableAt ℝ (f i xbar) ybar := fun i =>
      ((hd i xbar).differentiable one_ne_zero) ybar
    unfold lagrangian
    exact h0.add (DifferentiableAt.fun_sum fun i _ => (hi i).const_mul (U i))
  have hH : gy₀ + ∑ i, U i • gy i = 0 := by
    refine p52e8c78a_subgrad_zero (fun y => lagrangian f₀ f U xbar y) ybar _ hdiff
      hU.2.2 fun y => ?_
    have := hJ xbar y
    simpa using this
  intro x hx
  obtain ⟨y, hy⟩ := hWmin x hx
  rw [p52e8c78a_valueFn_eq f₀ f x y hy, p52e8c78a_valueFn_eq f₀ f xbar ybar hybar]
  have h1 := hJ x y
  rw [hH] at h1
  simp only [inner_zero_left, add_zero] at h1
  have hL : lagrangian f₀ f U x y ≤ f₀ x y := by
    unfold lagrangian
    have : ∑ i, U i * f i x y ≤ 0 :=
      Finset.sum_nonpos fun i _ => mul_nonpos_of_nonneg_of_nonpos (hU.1 i) (hy.1 i)
    linarith
  have hLbar : lagrangian f₀ f U xbar ybar = f₀ xbar ybar := by
    unfold lagrangian
    simp [hU.2.1]
  linarith

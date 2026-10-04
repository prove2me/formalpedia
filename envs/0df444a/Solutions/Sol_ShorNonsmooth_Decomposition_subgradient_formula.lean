-- Prove2me | solution 1 for ShorNonsmooth.Decomposition.subgradient_formula
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T13:23:30.978322+00:00
-- url     : https://prove2.me/submissions/9d43275e-48cc-47d3-92df-2389416ba388

import Mathlib
import Definitions.Def_ShorNonsmooth_Decomposition_ValueFunction

set_option autoImplicit false

open ShorNonsmooth.Decomposition in
theorem f9c887b8_valueFn_eq {l m n : ℕ}
    (f₀ : EuclideanSpace ℝ (Fin l) → EuclideanSpace ℝ (Fin m) → ℝ)
    (f : Fin n → EuclideanSpace ℝ (Fin l) → EuclideanSpace ℝ (Fin m) → ℝ)
    (x : EuclideanSpace ℝ (Fin l)) (y : EuclideanSpace ℝ (Fin m))
    (hy : IsOptimalY f₀ f x y) : valueFn f₀ f x = f₀ x y := by
  unfold valueFn
  apply IsLeast.csInf_eq
  refine ⟨⟨y, hy.1, rfl⟩, ?_⟩
  rintro _ ⟨y', hy', rfl⟩
  exact hy.2 y' hy'

open ShorNonsmooth.Decomposition in
theorem solution {l m n : ℕ}
    (f₀ : EuclideanSpace ℝ (Fin l) → EuclideanSpace ℝ (Fin m) → ℝ)
    (f : Fin n → EuclideanSpace ℝ (Fin l) → EuclideanSpace ℝ (Fin m) → ℝ)
    (hf₀ : JointlyConvex f₀) (hf : ∀ i, JointlyConvex (f i))
    (W : Set (EuclideanSpace ℝ (Fin l))) (hW : Convex ℝ W)
    (hWmin : ∀ x ∈ W, MinAttained f₀ f x)
    (xbar : EuclideanSpace ℝ (Fin l)) (hxbar : xbar ∈ W)
    (ybar : EuclideanSpace ℝ (Fin m)) (hybar : IsOptimalY f₀ f xbar ybar)
    (U : Fin n → ℝ) (hU : IsKuhnTuckerMultiplier f₀ f xbar ybar U)
    (gx : EuclideanSpace ℝ (Fin l)) (hgx : IsJointSubgradient (lagrangian f₀ f U) xbar ybar gx 0) :
    IsSubgradientOn (valueFn f₀ f) W xbar gx := by
  intro x hx
  obtain ⟨y, hy⟩ := hWmin x hx
  rw [f9c887b8_valueFn_eq f₀ f x y hy, f9c887b8_valueFn_eq f₀ f xbar ybar hybar]
  have h1 := hgx x y
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

-- Prove2me | solution 1 for OnlineConvexOpt.ConvexBasics.strong_convexity_smoothness_gap_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T07:06:35.667373+00:00
-- url     : https://prove2.me/submissions/7c37eae1-837d-446f-b093-7447785d6d70

import Mathlib
import Definitions.Def_OnlineConvexOpt_ConvexBasics_StronglyConvexOn
import Definitions.Def_OnlineConvexOpt_ConvexBasics_SmoothOn

set_option autoImplicit false

open scoped InnerProductSpace

/-- One gradient step of length `1/β` from `x` decreases a `β`-smooth `f` by `‖g x‖²/(2β)`. -/
theorem oco_smooth_step_descent {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (g : E → E) (β : ℝ) (hβ : 0 < β)
    (hsm : ∀ x y, f y ≤ f x + ⟪g x, y - x⟫_ℝ + (β / 2) * ‖y - x‖ ^ 2) (x : E) :
    f (x - (1 / β) • g x) ≤ f x - (1 / (2 * β)) * ‖g x‖ ^ 2 := by
  have h := hsm x (x - (1 / β) • g x)
  have e1 : x - (1 / β) • g x - x = -((1 / β) • g x) := by abel
  rw [e1, inner_neg_right, inner_smul_right, real_inner_self_eq_norm_sq, norm_neg,
    norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < 1 / β)] at h
  have e2 : f x + -(1 / β * ‖g x‖ ^ 2) + β / 2 * (1 / β * ‖g x‖) ^ 2
      = f x - (1 / (2 * β)) * ‖g x‖ ^ 2 := by
    field_simp
    ring
  linarith

/-- `⟪v, u⟫ + (α/2)‖u‖² ≥ -‖v‖²/(2α)`. -/
theorem oco_inner_quad_lower {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (α : ℝ) (hα : 0 < α) (v u : E) :
    -(1 / (2 * α)) * ‖v‖ ^ 2 ≤ ⟪v, u⟫_ℝ + (α / 2) * ‖u‖ ^ 2 := by
  have hcs : -(‖v‖ * ‖u‖) ≤ ⟪v, u⟫_ℝ := by
    have := abs_real_inner_le_norm v u
    linarith [neg_abs_le (⟪v, u⟫_ℝ)]
  have key : -(1 / (2 * α)) * ‖v‖ ^ 2 ≤ -(‖v‖ * ‖u‖) + (α / 2) * ‖u‖ ^ 2 := by
    have hsq : 0 ≤ (‖v‖ - α * ‖u‖) ^ 2 := sq_nonneg _
    have : -(1 / (2 * α)) * ‖v‖ ^ 2 - (-(‖v‖ * ‖u‖) + (α / 2) * ‖u‖ ^ 2)
        = -(1 / (2 * α)) * (‖v‖ - α * ‖u‖) ^ 2 := by
      field_simp
      ring
    have h2 : -(1 / (2 * α)) * (‖v‖ - α * ‖u‖) ^ 2 ≤ 0 := by
      have : 0 ≤ (1 / (2 * α)) * (‖v‖ - α * ‖u‖) ^ 2 := by positivity
      linarith
    linarith
  linarith

open OnlineConvexOpt.ConvexBasics in
theorem solution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (f : E → ℝ) (g : E → E)
    (hgrad : ∀ z, HasGradientAt f (g z) z)
    (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (xstar : E) (hxstar : IsMinOn f Set.univ xstar)
    (hsc : StronglyConvexOn Set.univ f g α) (hsm : SmoothOn Set.univ f g β)
    (x : E) :
    (α / 2) * ‖x - xstar‖ ^ 2 ≤ f x - f xstar ∧
      f x - f xstar ≤ (β / 2) * ‖x - xstar‖ ^ 2 ∧
      (1 / (2 * β)) * ‖g x‖ ^ 2 ≤ f x - f xstar ∧
      f x - f xstar ≤ (1 / (2 * α)) * ‖g x‖ ^ 2 := by
  have hsm' : ∀ x y, f y ≤ f x + ⟪g x, y - x⟫_ℝ + (β / 2) * ‖y - x‖ ^ 2 :=
    fun x y => hsm x (Set.mem_univ _) y (Set.mem_univ _)
  have hsc' : ∀ x y, f y ≥ f x + ⟪g x, y - x⟫_ℝ + (α / 2) * ‖y - x‖ ^ 2 :=
    fun x y => hsc x (Set.mem_univ _) y (Set.mem_univ _)
  have hmin : ∀ z, f xstar ≤ f z := fun z => hxstar (Set.mem_univ z)
  -- the gradient vanishes at the minimiser
  have hg0 : g xstar = 0 := by
    have h1 := oco_smooth_step_descent f g β hβ hsm' xstar
    have h2 := hmin (xstar - (1 / β) • g xstar)
    have h3 : (1 / (2 * β)) * ‖g xstar‖ ^ 2 ≤ 0 := by linarith
    have h4 : 0 < 1 / (2 * β) := by positivity
    have h5 : ‖g xstar‖ ^ 2 ≤ 0 := by
      by_contra hc
      rw [not_le] at hc
      have := mul_pos h4 hc
      linarith
    have h6 : ‖g xstar‖ = 0 := by
      have := sq_nonneg ‖g xstar‖
      nlinarith [norm_nonneg (g xstar)]
    exact norm_eq_zero.mp h6
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := hsc' xstar x
    rw [hg0, inner_zero_left] at h
    linarith
  · have h := hsm' xstar x
    rw [hg0, inner_zero_left] at h
    linarith
  · have h1 := oco_smooth_step_descent f g β hβ hsm' x
    have h2 := hmin (x - (1 / β) • g x)
    linarith
  · have h := hsc' x xstar
    have h2 := oco_inner_quad_lower α hα (g x) (xstar - x)
    linarith

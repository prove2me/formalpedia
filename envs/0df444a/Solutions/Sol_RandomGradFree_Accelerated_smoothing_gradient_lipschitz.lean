-- Prove2me | solution 1 for RandomGradFree.Accelerated.smoothing_gradient_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:50:30.232977+00:00
-- url     : https://prove2.me/submissions/b24fdf89-955c-41c7-9ed7-7d088b64081d

import Mathlib
import Definitions.Def_RandomGradFree_Shared_smoothing

open MeasureTheory ProbabilityTheory

namespace RandomGradFree.Accelerated

theorem aux_sgl_fderiv_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) (x : E) :
    fderiv ℝ f x = InnerProductSpace.toDual ℝ E (gradient f x) := by
  simp [gradient]

theorem aux_sgl_main {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (L₁ : ℝ) (hL₁ : 0 ≤ L₁) (hdiff : Differentiable ℝ f)
    (hL : ∀ x y, ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ L₁ * ‖x - y‖)
    (μ : ℝ) (hμ : 0 ≤ μ) (x₀ : E) :
    Integrable (fun u => fderiv ℝ f (x₀ + μ • u)) (stdGaussian E) ∧
    HasFDerivAt (RandomGradFree.Shared.smoothing f μ)
      (∫ u, fderiv ℝ f (x₀ + μ • u) ∂(stdGaussian E)) x₀ := by
  set γ := stdGaussian E with hγ
  set G := ‖fderiv ℝ f 0‖ with hG
  have hG0 : 0 ≤ G := norm_nonneg _
  have hfc : Continuous f := hdiff.continuous
  have hcont : Continuous (fderiv ℝ f) := by
    refine (LipschitzWith.of_dist_le_mul (K := L₁.toNNReal) fun a b => ?_).continuous
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hL₁]
    exact hL a b
  have hfd : ∀ z, ‖fderiv ℝ f z‖ ≤ G + L₁ * ‖z‖ := by
    intro z
    have := hL z 0
    simp only [sub_zero] at this
    have h2 := norm_sub_norm_le (fderiv ℝ f z) (fderiv ℝ f 0)
    linarith
  have hfb : ∀ z, ‖f z‖ ≤ ‖f 0‖ + (G + L₁ * ‖z‖) * ‖z‖ := by
    intro z
    have h := (convex_closedBall (0:E) ‖z‖).norm_image_sub_le_of_norm_fderiv_le
      (f := f) (C := G + L₁ * ‖z‖) (x := 0) (y := z) (fun w _ => hdiff w)
      (fun w hw => by
        have := hfd w
        rw [Metric.mem_closedBall, dist_zero_right] at hw
        nlinarith)
      (Metric.mem_closedBall_self (norm_nonneg z)) (by simp)
    simp only [sub_zero] at h
    have h2 := norm_sub_norm_le (f z) (f 0)
    linarith
  have hint1 : Integrable (fun u : E => ‖u‖) γ := IsGaussian.integrable_id.norm
  have hint2 : Integrable (fun u : E => ‖u‖ ^ 2) γ := by
    have := IsGaussian.memLp_id γ ((2 : ℕ) : ENNReal) (by simp)
    exact this.integrable_norm_pow two_ne_zero
  -- integrability of the derivative
  have hF'int : ∀ x : E, Integrable (fun u => fderiv ℝ f (x + μ • u)) γ := by
    intro x
    refine Integrable.mono' ((integrable_const (G + L₁ * ‖x‖)).add (hint1.const_mul (L₁ * μ)))
      ((hcont.comp (continuous_const.add (continuous_const.smul continuous_id))).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun u => ?_)
    have h1 := hfd (x + μ • u)
    have h2 : ‖x + μ • u‖ ≤ ‖x‖ + μ * ‖u‖ := by
      calc ‖x + μ • u‖ ≤ ‖x‖ + ‖μ • u‖ := norm_add_le _ _
        _ = ‖x‖ + μ * ‖u‖ := by rw [norm_smul, Real.norm_of_nonneg hμ]
    simp only [Pi.add_apply]
    nlinarith [mul_le_mul_of_nonneg_left h2 hL₁]
  refine ⟨hF'int x₀, ?_⟩
  show HasFDerivAt (fun x => ∫ u, f (x + μ • u) ∂γ) _ x₀
  have hF_int : Integrable (fun u => f (x₀ + μ • u)) γ := by
    refine Integrable.mono'
      (((integrable_const (‖f 0‖ + G * ‖x₀‖ + 2 * L₁ * ‖x₀‖ ^ 2)).add
        (hint1.const_mul (G * μ))).add (hint2.const_mul (2 * L₁ * μ ^ 2)))
      ((hfc.comp (continuous_const.add (continuous_const.smul continuous_id))).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun u => ?_)
    have h1 := hfb (x₀ + μ • u)
    have h2 : ‖x₀ + μ • u‖ ≤ ‖x₀‖ + μ * ‖u‖ := by
      calc ‖x₀ + μ • u‖ ≤ ‖x₀‖ + ‖μ • u‖ := norm_add_le _ _
        _ = ‖x₀‖ + μ * ‖u‖ := by rw [norm_smul, Real.norm_of_nonneg hμ]
    simp only [Pi.add_apply]
    set n := ‖x₀ + μ • u‖
    set a := ‖x₀‖
    set t := ‖u‖
    have hn : 0 ≤ n := norm_nonneg _
    have ha : 0 ≤ a := norm_nonneg _
    have ht : 0 ≤ t := norm_nonneg _
    have hs : 0 ≤ a + μ * t := by positivity
    have e1 : G * n ≤ G * (a + μ * t) := mul_le_mul_of_nonneg_left h2 hG0
    have e2 : n * n ≤ (a + μ * t) * (a + μ * t) := mul_le_mul h2 h2 hn hs
    have e3 : (a + μ * t) * (a + μ * t) ≤ 2 * a ^ 2 + 2 * μ ^ 2 * t ^ 2 := by
      nlinarith [sq_nonneg (a - μ * t)]
    have e4 : L₁ * (n * n) ≤ L₁ * (2 * a ^ 2 + 2 * μ ^ 2 * t ^ 2) :=
      mul_le_mul_of_nonneg_left (e2.trans e3) hL₁
    nlinarith
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun x u => f (x + μ • u)) (F' := fun x u => fderiv ℝ f (x + μ • u))
    (bound := fun u => G + L₁ * (‖x₀‖ + 1) + L₁ * μ * ‖u‖)
    (Metric.ball_mem_nhds x₀ one_pos)
    (Filter.Eventually.of_forall fun x =>
      (hfc.comp (continuous_const.add (continuous_const.smul continuous_id))).aestronglyMeasurable)
    hF_int
    ((hcont.comp (continuous_const.add (continuous_const.smul continuous_id))).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun u x hx => ?_)
    ((integrable_const _).add (hint1.const_mul (L₁ * μ)))
    (Filter.Eventually.of_forall fun u x _ => ?_)
  · have h1 := hfd (x + μ • u)
    have hx' : ‖x‖ ≤ ‖x₀‖ + 1 := by
      rw [Metric.mem_ball, dist_eq_norm] at hx
      have := norm_le_norm_add_norm_sub' x x₀
      calc ‖x‖ ≤ ‖x₀‖ + ‖x - x₀‖ := by
            have := norm_sub_norm_le x x₀
            linarith
        _ ≤ ‖x₀‖ + 1 := by linarith
    have h2 : ‖x + μ • u‖ ≤ ‖x₀‖ + 1 + μ * ‖u‖ := by
      calc ‖x + μ • u‖ ≤ ‖x‖ + ‖μ • u‖ := norm_add_le _ _
        _ = ‖x‖ + μ * ‖u‖ := by rw [norm_smul, Real.norm_of_nonneg hμ]
        _ ≤ ‖x₀‖ + 1 + μ * ‖u‖ := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h2 hL₁]
  · exact (hasFDerivAt_comp_add_right (μ • u)).2 (hdiff _).hasFDerivAt

end RandomGradFree.Accelerated

open RandomGradFree.Accelerated
open MeasureTheory ProbabilityTheory

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (L₁ : ℝ) (hL₁ : 0 ≤ L₁) (hdiff : Differentiable ℝ f)
    (hgrad : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L₁ * ‖x - y‖)
    (μ : ℝ) (hμ : 0 ≤ μ) :
    Differentiable ℝ (RandomGradFree.Shared.smoothing f μ) ∧
      ∀ x y, ‖gradient (RandomGradFree.Shared.smoothing f μ) x - gradient (RandomGradFree.Shared.smoothing f μ) y‖ ≤ L₁ * ‖x - y‖ := by
  have hL : ∀ x y, ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ L₁ * ‖x - y‖ := by
    intro x y
    rw [aux_sgl_fderiv_eq f x, aux_sgl_fderiv_eq f y, ← map_sub,
      LinearIsometryEquiv.norm_map]
    exact hgrad x y
  have hmain := aux_sgl_main f L₁ hL₁ hdiff hL μ hμ
  refine ⟨fun x => (hmain x).2.differentiableAt, fun x y => ?_⟩
  have hgx : gradient (RandomGradFree.Shared.smoothing f μ) x =
      (InnerProductSpace.toDual ℝ E).symm
        (∫ u, fderiv ℝ f (x + μ • u) ∂(stdGaussian E)) := by
    simp only [gradient, (hmain x).2.fderiv]
  have hgy : gradient (RandomGradFree.Shared.smoothing f μ) y =
      (InnerProductSpace.toDual ℝ E).symm
        (∫ u, fderiv ℝ f (y + μ • u) ∂(stdGaussian E)) := by
    simp only [gradient, (hmain y).2.fderiv]
  rw [hgx, hgy, ← map_sub, LinearIsometryEquiv.norm_map,
    ← integral_sub (hmain x).1 (hmain y).1]
  have := norm_integral_le_of_norm_le_const (μ := stdGaussian E)
    (f := fun u => fderiv ℝ f (x + μ • u) - fderiv ℝ f (y + μ • u)) (C := L₁ * ‖x - y‖)
    (Filter.Eventually.of_forall fun u => by
      have := hL (x + μ • u) (y + μ • u)
      simpa using this)
  simpa using this

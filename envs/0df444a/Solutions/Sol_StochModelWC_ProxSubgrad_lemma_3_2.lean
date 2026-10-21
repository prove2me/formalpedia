-- Prove2me | solution 1 for StochModelWC.ProxSubgrad.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T01:51:18.890988+00:00
-- url     : https://prove2.me/submissions/2a19c776-0734-4f77-8e22-2fbdfed19e36

import Mathlib
import Definitions.Def_StochModelWC_ProxSubgrad_Basic

set_option autoImplicit false
open MeasureTheory Filter Topology StochModelWC.ProxSubgrad
open scoped InnerProductSpace

theorem smw_frechet_global {d : ℕ} (D : Set (EuclideanSpace ℝ (Fin d)))
    (r : EuclideanSpace ℝ (Fin d) → ℝ) (hconv : ConvexOn ℝ D r)
    (x w : EuclideanSpace ℝ (Fin d)) (hw : w ∈ frechetSubdiff D r x) :
    x ∈ D ∧ ∀ y ∈ D, r x + ⟪w, y - x⟫_ℝ ≤ r y := by
  classical
  have hw' := hw
  unfold frechetSubdiff NonconvexSplitting.Shared.IsRegularSubgrad at hw'
  obtain ⟨h1, h2⟩ := hw'
  have hxD : x ∈ D := by
    by_contra h
    simp [h] at h1
  refine ⟨hxD, fun y hyD => ?_⟩
  -- for every ε > 0
  have key : ∀ ε : ℝ, 0 < ε → ⟪w, y - x⟫_ℝ - ε * ‖y - x‖ ≤ r y - r x := by
    intro ε hε
    have hev := h2 ε hε
    have hcont : Tendsto (fun s : ℝ => x + s • (y - x)) (𝓝 0) (𝓝 x) := by
      have : Continuous (fun s : ℝ => x + s • (y - x)) := by fun_prop
      simpa using this.tendsto 0
    have hev' : ∀ᶠ s : ℝ in 𝓝[>] 0, _ := (hcont.mono_left nhdsWithin_le_nhds).eventually hev
    obtain ⟨s, hs, hs0⟩ := (hev'.and (Ioo_mem_nhdsGT (zero_lt_one : (0:ℝ) < 1))).exists
    obtain ⟨hs0', hs1⟩ := hs0
    have hzD : x + s • (y - x) ∈ D := hconv.1.add_smul_sub_mem hxD hyD ⟨hs0'.le, hs1.le⟩
    have hcv := hconv.2 hxD hyD (by linarith : (0:ℝ) ≤ 1 - s) hs0'.le (by ring)
    have e1 : (1 - s) • x + s • y = x + s • (y - x) := by module
    rw [e1] at hcv
    simp only [hxD, hzD, if_true] at hs
    rw [← EReal.coe_add, EReal.coe_le_coe_iff] at hs
    have e2 : x + s • (y - x) - x = s • (y - x) := by abel
    rw [e2, inner_smul_right, norm_smul, Real.norm_of_nonneg hs0'.le] at hs
    simp only [smul_eq_mul] at hcv
    have : s * (⟪w, y - x⟫_ℝ - ε * ‖y - x‖) ≤ s * (r y - r x) := by nlinarith
    exact le_of_mul_le_mul_left this hs0'
  have : ⟪w, y - x⟫_ℝ - (r y - r x) ≤ 0 := by
    apply le_of_forall_pos_le_add
    intro η hη
    have hn : 0 ≤ ‖y - x‖ := norm_nonneg _
    have := key (η / (‖y - x‖ + 1)) (by positivity)
    have h3 : η / (‖y - x‖ + 1) * ‖y - x‖ ≤ η := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  linarith

theorem solution {d : ℕ} (D : Set (EuclideanSpace ℝ (Fin d)))
    (f r : EuclideanSpace ℝ (Fin d) → ℝ) (ρ ρbar α : ℝ)
    (hD : D.Nonempty) (hr_cl : StochModelWC.ModelBased.IsClosedFn D r) (hr_cvx : ConvexOn ℝ D r)
    (hf : StochModelWC.ModelBased.IsWeaklyConvexOn Set.univ ρ f) (hρbar : ρ < ρbar) (hα : 0 < α)
    (x xhat vhat : EuclideanSpace ℝ (Fin d)) (hx : x ∈ D)
    (hxhat : StochModelWC.ModelBased.IsProxPt D (fun y => f y + r y) (1 / ρbar) x xhat)
    (hvhat : vhat ∈ frechetSubdiff Set.univ f xhat)
    (hvhat_r : ρbar • (x - xhat) - vhat ∈ frechetSubdiff D r xhat) :
    StochModelWC.ModelBased.IsProxPt D r α ((α * ρbar) • x - α • vhat + (1 - α * ρbar) • xhat) xhat := by
  obtain ⟨hxhD, hglob⟩ := smw_frechet_global D r hr_cvx xhat _ hvhat_r
  refine ⟨hxhD, fun y hy => ?_⟩
  set w : EuclideanSpace ℝ (Fin d) := ρbar • (x - xhat) - vhat with hw
  have hz : (α * ρbar) • x - α • vhat + (1 - α * ρbar) • xhat = xhat + α • w := by
    rw [hw]; module
  rw [hz]
  have e1 : xhat - (xhat + α • w) = -(α • w) := by abel
  have e2 : y - (xhat + α • w) = (y - xhat) - α • w := by abel
  rw [e1, e2, norm_neg, norm_smul, norm_sub_sq_real, inner_smul_right, norm_smul,
    Real.norm_of_nonneg hα.le, real_inner_comm]
  have hg := hglob y hy
  have hA : 0 ≤ ‖y - xhat‖ ^ 2 / (2 * α) := by positivity
  have e3 : 1 / (2 * α) * (α * ‖w‖) ^ 2 = α * ‖w‖ ^ 2 / 2 := by field_simp
  have e4 : 1 / (2 * α) * (‖y - xhat‖ ^ 2 - 2 * (α * ⟪w, y - xhat⟫_ℝ) + (α * ‖w‖) ^ 2)
      = ‖y - xhat‖ ^ 2 / (2 * α) - ⟪w, y - xhat⟫_ℝ + α * ‖w‖ ^ 2 / 2 := by
    field_simp
  rw [e3, e4]
  linarith

-- Prove2me | solution 1 for SurrogateOps.corollary_5_gradient
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T23:45:37.211057+00:00
-- url     : https://prove2.me/submissions/aed79e19-b76b-4ffd-971c-db4199be6c6d

import Mathlib
import Definitions.Def_SurrogateOps_GradAccAt
import Definitions.Def_SurrogateOps_GradAccNear
import Definitions.Def_SurrogateOps_UnifBddAt
import Definitions.Def_SurrogateOps_UnifBddNear

open SurrogateOps in
theorem solution {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (fm : ℝ → EuclideanSpace ℝ (Fin d) → ℝ) (x0 : EuclideanSpace ℝ (Fin d)) (Δbar N κ : ℝ)
    (hΔbar : 0 < Δbar) (hf : ContDiff ℝ 1 f) :
    (GradAccAt f fm x0 Δbar N κ →
        UnifBddAt (fun Δ x => ‖fderiv ℝ (fm Δ) x‖) x0 Δbar) ∧
      (GradAccNear f fm x0 Δbar N κ →
        UnifBddNear (fun Δ x => ‖fderiv ℝ (fm Δ) x‖) x0 Δbar) := by
  have tri : ∀ (a b : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ), ‖b‖ ≤ ‖a‖ + ‖a - b‖ := by
    intro a b
    calc ‖b‖ = ‖a - (a - b)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖a‖ + ‖a - b‖ := norm_sub_le _ _
  constructor
  · rintro ⟨hN, hκ, h⟩
    refine ⟨‖fderiv ℝ f x0‖ + κ * Δbar ^ N,
      add_nonneg (norm_nonneg _) (mul_nonneg hκ (Real.rpow_nonneg hΔbar.le _)), fun Δ hΔ => ?_⟩
    show |‖fderiv ℝ (fm Δ) x0‖| ≤ _
    rw [abs_norm]
    have h1 := h Δ hΔ
    have h2 : Δ ^ N ≤ Δbar ^ N := Real.rpow_le_rpow hΔ.1.le hΔ.2 hN
    have h3 := tri (fderiv ℝ f x0) (fderiv ℝ (fm Δ) x0)
    nlinarith [mul_le_mul_of_nonneg_left h2 hκ]
  · rintro ⟨hN, hκ, h⟩
    have hcont : Continuous fun x => fderiv ℝ f x := hf.continuous_fderiv one_ne_zero
    obtain ⟨B, hB⟩ := (isCompact_closedBall x0 Δbar).exists_bound_of_continuousOn
      hcont.continuousOn
    refine ⟨max B 0 + κ * Δbar ^ N,
      add_nonneg (le_max_right _ _) (mul_nonneg hκ (Real.rpow_nonneg hΔbar.le _)),
      fun Δ hΔ x hx => ?_⟩
    show |‖fderiv ℝ (fm Δ) x‖| ≤ _
    rw [abs_norm]
    have h1 := h Δ hΔ x hx
    have h2 : Δ ^ N ≤ Δbar ^ N := Real.rpow_le_rpow hΔ.1.le hΔ.2 hN
    have h3 := tri (fderiv ℝ f x) (fderiv ℝ (fm Δ) x)
    have hx' : x ∈ Metric.closedBall x0 Δbar := Metric.closedBall_subset_closedBall hΔ.2 hx
    have h4 := le_trans (hB x hx') (le_max_left B 0)
    nlinarith [mul_le_mul_of_nonneg_left h2 hκ]

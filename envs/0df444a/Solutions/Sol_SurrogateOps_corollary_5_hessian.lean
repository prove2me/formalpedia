-- Prove2me | solution 1 for SurrogateOps.corollary_5_hessian
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T12:22:29.72203+00:00
-- url     : https://prove2.me/submissions/28708be6-16d3-47a1-971f-719732c55996

import Mathlib
import Definitions.Def_SurrogateOps_HessAccAt
import Definitions.Def_SurrogateOps_HessAccNear
import Definitions.Def_SurrogateOps_UnifBddAt
import Definitions.Def_SurrogateOps_UnifBddNear

open SurrogateOps in
theorem solution {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (fm : ℝ → EuclideanSpace ℝ (Fin d) → ℝ) (x0 : EuclideanSpace ℝ (Fin d)) (Δbar N κ : ℝ)
    (hΔbar : 0 < Δbar) (hf : ContDiff ℝ 2 f) :
    (HessAccAt f fm x0 Δbar N κ →
        UnifBddAt (fun Δ x => ‖fderiv ℝ (fderiv ℝ (fm Δ)) x‖) x0 Δbar) ∧
      (HessAccNear f fm x0 Δbar N κ →
        UnifBddNear (fun Δ x => ‖fderiv ℝ (fderiv ℝ (fm Δ)) x‖) x0 Δbar) := by
  have hpow : ∀ Δ ∈ Set.Ioc 0 Δbar, 0 ≤ N → Δ ^ N ≤ Δbar ^ N := fun Δ hΔ hN =>
    Real.rpow_le_rpow hΔ.1.le hΔ.2 hN
  constructor
  · rintro ⟨hN, hκ, h⟩
    refine ⟨‖fderiv ℝ (fderiv ℝ f) x0‖ + κ * Δbar ^ N, ?_, ?_⟩
    · have := Real.rpow_nonneg hΔbar.le N
      positivity
    · intro Δ hΔ
      dsimp only
      refine (abs_of_nonneg (norm_nonneg (fderiv ℝ (fderiv ℝ (fm Δ)) x0))).trans_le ?_
      have h1 := h Δ hΔ
      have h2 := abs_norm_sub_norm_le (fderiv ℝ (fderiv ℝ f) x0) (fderiv ℝ (fderiv ℝ (fm Δ)) x0)
      have h2' := neg_le_abs (‖fderiv ℝ (fderiv ℝ f) x0‖ - ‖fderiv ℝ (fderiv ℝ (fm Δ)) x0‖)
      have h3 := mul_le_mul_of_nonneg_left (hpow Δ hΔ hN) hκ
      linarith
  · rintro ⟨hN, hκ, h⟩
    have hc := (hf.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
    obtain ⟨C, hC⟩ := (isCompact_closedBall x0 Δbar).exists_bound_of_continuousOn hc.continuousOn
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC x0 (Metric.mem_closedBall_self hΔbar.le))
    refine ⟨C + κ * Δbar ^ N, ?_, ?_⟩
    · have := Real.rpow_nonneg hΔbar.le N
      positivity
    · intro Δ hΔ x hx
      dsimp only
      refine (abs_of_nonneg (norm_nonneg (fderiv ℝ (fderiv ℝ (fm Δ)) x))).trans_le ?_
      have h1 := h Δ hΔ x hx
      have h2 := abs_norm_sub_norm_le (fderiv ℝ (fderiv ℝ f) x) (fderiv ℝ (fderiv ℝ (fm Δ)) x)
      have h2' := neg_le_abs (‖fderiv ℝ (fderiv ℝ f) x‖ - ‖fderiv ℝ (fderiv ℝ (fm Δ)) x‖)
      have h3 := mul_le_mul_of_nonneg_left (hpow Δ hΔ hN) hκ
      have h4 := hC x (Metric.closedBall_subset_closedBall hΔ.2 hx)
      linarith

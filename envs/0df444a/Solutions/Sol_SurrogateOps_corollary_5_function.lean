-- Prove2me | solution 1 for SurrogateOps.corollary_5_function
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T22:01:46.201322+00:00
-- url     : https://prove2.me/submissions/6f56c8b5-acb9-44a5-9f8b-d6df53de5741

import Mathlib
import Definitions.Def_SurrogateOps_FunAccAt
import Definitions.Def_SurrogateOps_FunAccNear
import Definitions.Def_SurrogateOps_UnifBddAt
import Definitions.Def_SurrogateOps_UnifBddNear

open SurrogateOps in
theorem solution {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (fm : ℝ → EuclideanSpace ℝ (Fin d) → ℝ) (x0 : EuclideanSpace ℝ (Fin d)) (Δbar N κ : ℝ)
    (hΔbar : 0 < Δbar) (hf : Continuous f) :
    (FunAccAt f fm x0 Δbar N κ → UnifBddAt fm x0 Δbar) ∧
      (FunAccNear f fm x0 Δbar N κ → UnifBddNear fm x0 Δbar) := by
  have hpow : ∀ Δ ∈ Set.Ioc 0 Δbar, 0 ≤ N → Δ ^ N ≤ Δbar ^ N := fun Δ hΔ hN =>
    Real.rpow_le_rpow hΔ.1.le hΔ.2 hN
  have hbar0 : 0 ≤ Δbar ^ N := Real.rpow_nonneg hΔbar.le _
  refine ⟨fun ⟨hN, hκ, h⟩ => ?_, fun ⟨hN, hκ, h⟩ => ?_⟩
  · refine ⟨|f x0| + κ * Δbar ^ N, by positivity, fun Δ hΔ => ?_⟩
    have h1 := h Δ hΔ
    have h2 := abs_sub_abs_le_abs_sub (fm Δ x0) (f x0)
    rw [abs_sub_comm] at h2
    have h3 := mul_le_mul_of_nonneg_left (hpow Δ hΔ hN) hκ
    linarith
  · obtain ⟨C, hC⟩ := (isCompact_closedBall x0 Δbar).exists_bound_of_continuousOn
      hf.continuousOn
    refine ⟨max C 0 + κ * Δbar ^ N, by positivity, fun Δ hΔ x hx => ?_⟩
    have hx' : x ∈ Metric.closedBall x0 Δbar := Metric.closedBall_subset_closedBall hΔ.2 hx
    have h0 := hC x hx'
    rw [Real.norm_eq_abs] at h0
    have h1 := h Δ hΔ x hx
    have h2 := abs_sub_abs_le_abs_sub (fm Δ x) (f x)
    rw [abs_sub_comm] at h2
    have h3 := mul_le_mul_of_nonneg_left (hpow Δ hΔ hN) hκ
    have h4 := le_max_left C 0
    linarith

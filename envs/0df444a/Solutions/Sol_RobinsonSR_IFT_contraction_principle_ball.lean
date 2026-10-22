-- Prove2me | solution 1 for RobinsonSR.IFT.contraction_principle_ball
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T00:07:57.352331+00:00
-- url     : https://prove2.me/submissions/3d5ef982-7ccb-4334-a48a-08b0a089ea6e

import Mathlib



namespace RobinsonSR.IFT

open scoped Topology

theorem cp_gen_core {α : Type*} [MetricSpace α] (S : Set α) (hS : IsComplete S)
    (x : α) (hx : x ∈ S) (Φ : α → α) (hmaps : Set.MapsTo Φ S S)
    (kappa : ℝ) (hk0 : 0 ≤ kappa) (hk1 : kappa < 1)
    (hcontr : ∀ x₁ ∈ S, ∀ x₂ ∈ S, dist (Φ x₁) (Φ x₂) ≤ kappa * dist x₁ x₂) :
    ∃ xp ∈ S, Φ xp = xp := by
  have hK : ContractingWith (Real.toNNReal kappa) (hmaps.restrict Φ S S) := by
    refine ⟨?_, ?_⟩
    · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hk0]; simpa using hk1
    · refine LipschitzWith.of_dist_le_mul fun a b => ?_
      rw [Real.coe_toNNReal _ hk0]
      exact hcontr a a.2 b b.2
  obtain ⟨y, hyS, hy, -⟩ := hK.exists_fixedPoint' hS hmaps hx (edist_ne_top _ _)
  exact ⟨y, hyS, hy⟩

theorem cpb_core {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (x0 : X) (rho : ℝ) (hrho : 0 < rho) (Φ : X → X)
    (hmaps : Set.MapsTo Φ (Metric.closedBall x0 rho) (Metric.closedBall x0 rho))
    (kappa : ℝ) (hk0 : 0 ≤ kappa) (hk1 : kappa < 1)
    (hcontr : ∀ x₁ ∈ Metric.closedBall x0 rho, ∀ x₂ ∈ Metric.closedBall x0 rho,
      ‖Φ x₁ - Φ x₂‖ ≤ kappa * ‖x₁ - x₂‖) :
    ∃ xp ∈ Metric.closedBall x0 rho, Φ xp = xp ∧
      (∀ z ∈ Metric.closedBall x0 rho, Φ z = z → z = xp) ∧
      ∀ x ∈ Metric.closedBall x0 rho, ‖xp - x‖ ≤ (1 - kappa)⁻¹ * ‖Φ x - x‖ := by
  obtain ⟨xp, hxp, hfix⟩ := cp_gen_core (Metric.closedBall x0 rho)
    Metric.isClosed_closedBall.isComplete x0 (Metric.mem_closedBall_self hrho.le) Φ hmaps
    kappa hk0 hk1 (by
      intro a ha b hb; rw [dist_eq_norm, dist_eq_norm]; exact hcontr a ha b hb)
  refine ⟨xp, hxp, hfix, ?_, ?_⟩
  · intro z hz hzf
    have h := hcontr z hz xp hxp
    rw [hzf, hfix] at h
    have : ‖z - xp‖ = 0 := by nlinarith [norm_nonneg (z - xp)]
    exact sub_eq_zero.mp (norm_eq_zero.mp this)
  · intro x hx
    have h := hcontr xp hxp x hx
    rw [hfix] at h
    have htri : ‖xp - x‖ ≤ ‖xp - Φ x‖ + ‖Φ x - x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    have h1 : 0 < 1 - kappa := by linarith
    rw [le_inv_mul_iff₀ h1]
    nlinarith

end RobinsonSR.IFT

open RobinsonSR.IFT


theorem solution {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (x0 : X) (rho : ℝ) (hrho : 0 < rho) (Φ : X → X)
    (hmaps : Set.MapsTo Φ (Metric.closedBall x0 rho) (Metric.closedBall x0 rho))
    (kappa : ℝ) (hk0 : 0 ≤ kappa) (hk1 : kappa < 1)
    (hcontr : ∀ x₁ ∈ Metric.closedBall x0 rho, ∀ x₂ ∈ Metric.closedBall x0 rho,
      ‖Φ x₁ - Φ x₂‖ ≤ kappa * ‖x₁ - x₂‖) :
    ∃ xp ∈ Metric.closedBall x0 rho, Φ xp = xp ∧
      (∀ z ∈ Metric.closedBall x0 rho, Φ z = z → z = xp) ∧
      ∀ x ∈ Metric.closedBall x0 rho, ‖xp - x‖ ≤ (1 - kappa)⁻¹ * ‖Φ x - x‖ := by
  exact cpb_core x0 rho hrho Φ hmaps kappa hk0 hk1 hcontr

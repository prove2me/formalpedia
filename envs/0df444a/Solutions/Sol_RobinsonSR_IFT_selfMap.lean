-- Prove2me | solution 1 for RobinsonSR.IFT.selfMap
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T00:08:00.383381+00:00
-- url     : https://prove2.me/submissions/8f42b00e-9af6-4604-8d34-57433d693534

import Mathlib
import Definitions.Def_RobinsonSR_IFT_Setting



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

theorem fps_core {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (C : Set X) {P : Type*} (p0 : P) (x0 : X)
    (f : P → X → StrongDual ℝ X) (f' : P → X → (X →L[ℝ] StrongDual ℝ X))
    (U : Set (StrongDual ℝ X)) (V : Set X) (s : StrongDual ℝ X → X)
    (hs : ∀ y ∈ U, s y ∈ V ∧ y - (f p0 x0 + f' p0 x0 (s y - x0)) ∈ normalCone C (s y) ∧
      ∀ z ∈ V, y - (f p0 x0 + f' p0 x0 (z - x0)) ∈ normalCone C z → z = s y)
    (rho : ℝ) (hball : Metric.closedBall x0 rho ⊆ V) (p : P)
    (hU : ∀ x ∈ Metric.closedBall x0 rho, residual f f' p0 x0 p x ∈ U) :
    ∀ x ∈ Metric.closedBall x0 rho,
      (s (residual f f' p0 x0 p x) = x ↔ -(f p x) ∈ normalCone C x) := by
  intro x hx
  have hy := hs _ (hU x hx)
  have heq : residual f f' p0 x0 p x - (f p0 x0 + f' p0 x0 (x - x0)) = -(f p x) := by
    unfold residual; abel
  constructor
  · intro h
    have := hy.2.1
    rw [h, heq] at this
    exact this
  · intro h
    rw [← heq] at h
    exact (hy.2.2 x (hball hx) h).symm

theorem rlip_core {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (Ω : Set X) {P : Type*} (p0 : P) (x0 : X)
    (f : P → X → StrongDual ℝ X) (f' : P → X → (X →L[ℝ] StrongDual ℝ X))
    (hf' : ∀ p, ∀ x ∈ Ω, HasFDerivAt (f p) (f' p x) x)
    (rho delta : ℝ) (hballΩ : Metric.closedBall x0 rho ⊆ Ω) (p : P)
    (hdelta : ∀ x ∈ Metric.closedBall x0 rho, ‖f' p x - f' p0 x0‖ ≤ delta) :
    ∀ x₁ ∈ Metric.closedBall x0 rho, ∀ x₂ ∈ Metric.closedBall x0 rho,
      ‖residual f f' p0 x0 p x₁ - residual f f' p0 x0 p x₂‖ ≤ delta * ‖x₁ - x₂‖ := by
  intro x₁ h1 x₂ h2
  have h := (convex_closedBall x0 rho).norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (f := f p) (f' := f' p) (φ := f' p0 x0)
    (fun x hx => (hf' p x (hballΩ hx)).hasFDerivWithinAt) hdelta h2 h1
  have heq : residual f f' p0 x0 p x₁ - residual f f' p0 x0 p x₂ =
      -(f p x₁ - f p x₂ - f' p0 x0 (x₁ - x₂)) := by
    unfold residual; rw [map_sub, map_sub, map_sub]; abel
  rw [heq, norm_neg]; exact h

theorem ce_core {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (Ω : Set X) {P : Type*} (p0 : P) (x0 : X)
    (f : P → X → StrongDual ℝ X) (f' : P → X → (X →L[ℝ] StrongDual ℝ X))
    (hf' : ∀ p, ∀ x ∈ Ω, HasFDerivAt (f p) (f' p x) x)
    (U : Set (StrongDual ℝ X)) (s : StrongDual ℝ X → X) (lam : ℝ) (hlam : 0 ≤ lam)
    (hsL : ∀ y₁ ∈ U, ∀ y₂ ∈ U, ‖s y₁ - s y₂‖ ≤ lam * ‖y₁ - y₂‖)
    (rho delta : ℝ) (hdelta0 : 0 < delta) (hballΩ : Metric.closedBall x0 rho ⊆ Ω) (p : P)
    (hU : ∀ x ∈ Metric.closedBall x0 rho, residual f f' p0 x0 p x ∈ U)
    (hdelta : ∀ x ∈ Metric.closedBall x0 rho, ‖f' p x - f' p0 x0‖ ≤ delta) :
    ∀ x₁ ∈ Metric.closedBall x0 rho, ∀ x₂ ∈ Metric.closedBall x0 rho,
      ‖s (residual f f' p0 x0 p x₁) - s (residual f f' p0 x0 p x₂)‖ ≤
        lam * delta * ‖x₁ - x₂‖ := by
  intro x₁ h1 x₂ h2
  have := rlip_core Ω p0 x0 f f' hf' rho delta hballΩ p hdelta x₁ h1 x₂ h2
  calc _ ≤ lam * ‖residual f f' p0 x0 p x₁ - residual f f' p0 x0 p x₂‖ :=
        hsL _ (hU x₁ h1) _ (hU x₂ h2)
    _ ≤ lam * (delta * ‖x₁ - x₂‖) := mul_le_mul_of_nonneg_left this hlam
    _ = _ := by ring

theorem sm_core {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (C : Set X) (Ω : Set X) {P : Type*} (p0 : P) (x0 : X)
    (f : P → X → StrongDual ℝ X) (f' : P → X → (X →L[ℝ] StrongDual ℝ X))
    (hf' : ∀ p, ∀ x ∈ Ω, HasFDerivAt (f p) (f' p x) x)
    (hsol : -(f p0 x0) ∈ normalCone C x0)
    (U : Set (StrongDual ℝ X)) (V : Set X) (s : StrongDual ℝ X → X)
    (hs : ∀ y ∈ U, s y ∈ V ∧ y - (f p0 x0 + f' p0 x0 (s y - x0)) ∈ normalCone C (s y) ∧
      ∀ z ∈ V, y - (f p0 x0 + f' p0 x0 (z - x0)) ∈ normalCone C z → z = s y)
    (hU0 : (0 : StrongDual ℝ X) ∈ U)
    (lam : ℝ) (hlam : 0 ≤ lam)
    (hsL : ∀ y₁ ∈ U, ∀ y₂ ∈ U, ‖s y₁ - s y₂‖ ≤ lam * ‖y₁ - y₂‖)
    (rho delta : ℝ) (hrho : 0 < rho) (hdelta0 : 0 < delta) (hlamdelta : lam * delta < 1)
    (hball : Metric.closedBall x0 rho ⊆ V ∩ Ω) (p : P)
    (hU : ∀ x ∈ Metric.closedBall x0 rho, residual f f' p0 x0 p x ∈ U)
    (hdelta : ∀ x ∈ Metric.closedBall x0 rho, ‖f' p x - f' p0 x0‖ ≤ delta)
    (hN : lam * ‖f p0 x0 - f p x0‖ ≤ (1 - lam * delta) * rho) :
    ∀ x ∈ Metric.closedBall x0 rho,
      s (residual f f' p0 x0 p x) ∈ Metric.closedBall x0 rho := by
  intro x hx
  have hx0 : x0 ∈ Metric.closedBall x0 rho := Metric.mem_closedBall_self hrho.le
  have hs0 : x0 = s 0 := by
    refine (hs 0 hU0).2.2 x0 (hball hx0).1 ?_
    simpa using hsol
  have hr0 : residual f f' p0 x0 p x0 = f p0 x0 - f p x0 := by
    unfold residual; simp
  have hA := ce_core Ω p0 x0 f f' hf' U s lam hlam hsL rho delta hdelta0
    (fun z hz => (hball hz).2) p hU hdelta x hx x0 hx0
  have hB : ‖s (residual f f' p0 x0 p x0) - s 0‖ ≤ lam * ‖f p0 x0 - f p x0‖ := by
    have := hsL _ (hU x0 hx0) 0 hU0
    rw [hr0]; rwa [sub_zero, hr0] at this
  rw [Metric.mem_closedBall, dist_eq_norm]
  rw [Metric.mem_closedBall, dist_eq_norm] at hx
  have htri : ‖s (residual f f' p0 x0 p x) - x0‖ ≤
      ‖s (residual f f' p0 x0 p x) - s (residual f f' p0 x0 p x0)‖ +
      ‖s (residual f f' p0 x0 p x0) - x0‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
  rw [← hs0] at hB
  have : lam * delta * ‖x - x0‖ ≤ lam * delta * rho :=
    mul_le_mul_of_nonneg_left hx (mul_nonneg hlam hdelta0.le)
  nlinarith

end RobinsonSR.IFT

open RobinsonSR.IFT


theorem solution {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (C : Set X) (Ω : Set X) {P : Type*} (p0 : P) (x0 : X)
    (f : P → X → StrongDual ℝ X) (f' : P → X → (X →L[ℝ] StrongDual ℝ X))
    (hf' : ∀ p, ∀ x ∈ Ω, HasFDerivAt (f p) (f' p x) x)
    (hsol : -(f p0 x0) ∈ normalCone C x0)
    (U : Set (StrongDual ℝ X)) (V : Set X) (s : StrongDual ℝ X → X)
    (hs : ∀ y ∈ U, s y ∈ V ∧ y - (f p0 x0 + f' p0 x0 (s y - x0)) ∈ normalCone C (s y) ∧
      ∀ z ∈ V, y - (f p0 x0 + f' p0 x0 (z - x0)) ∈ normalCone C z → z = s y)
    (hU0 : (0 : StrongDual ℝ X) ∈ U)
    (lam : ℝ) (hlam : 0 ≤ lam)
    (hsL : ∀ y₁ ∈ U, ∀ y₂ ∈ U, ‖s y₁ - s y₂‖ ≤ lam * ‖y₁ - y₂‖)
    (rho delta : ℝ) (hrho : 0 < rho) (hdelta0 : 0 < delta) (hlamdelta : lam * delta < 1)
    (hball : Metric.closedBall x0 rho ⊆ V ∩ Ω) (p : P)
    (hU : ∀ x ∈ Metric.closedBall x0 rho, residual f f' p0 x0 p x ∈ U)
    (hdelta : ∀ x ∈ Metric.closedBall x0 rho, ‖f' p x - f' p0 x0‖ ≤ delta)
    (hN : lam * ‖f p0 x0 - f p x0‖ ≤ (1 - lam * delta) * rho) :
    ∀ x ∈ Metric.closedBall x0 rho,
      s (residual f f' p0 x0 p x) ∈ Metric.closedBall x0 rho := by
  exact sm_core C Ω p0 x0 f f' hf' hsol U V s hs hU0 lam hlam hsL rho delta hrho hdelta0 hlamdelta hball p hU hdelta hN

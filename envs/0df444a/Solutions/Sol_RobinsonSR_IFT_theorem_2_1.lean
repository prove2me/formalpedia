-- Prove2me | solution 1 for RobinsonSR.IFT.theorem_2_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T00:15:19.163737+00:00
-- url     : https://prove2.me/submissions/9e917cf4-0c68-4ad0-9e13-d6b8d3d7ac25

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

theorem ub_core {X : Type*} [NormedAddCommGroup X] (B : Set X) (Φ : X → X)
    (kappa : ℝ) (hk1 : kappa < 1)
    (hcontr : ∀ x₁ ∈ B, ∀ x₂ ∈ B, ‖Φ x₁ - Φ x₂‖ ≤ kappa * ‖x₁ - x₂‖)
    (xp : X) (hxp : xp ∈ B) (hfix : Φ xp = xp) :
    (∀ z ∈ B, Φ z = z → z = xp) ∧
      ∀ x ∈ B, ‖xp - x‖ ≤ (1 - kappa)⁻¹ * ‖Φ x - x‖ := by
  refine ⟨?_, ?_⟩
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

theorem t21_core {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (C : Set X) (hC : IsClosed C) (hCc : Convex ℝ C)
    (Ω : Set X) (hΩ : IsOpen Ω) (x0 : X) (hx0 : x0 ∈ Ω)
    {P : Type*} [TopologicalSpace P] (p0 : P)
    (f : P → X → StrongDual ℝ X) (f' : P → X → (X →L[ℝ] StrongDual ℝ X))
    (hf' : ∀ p, ∀ x ∈ Ω, HasFDerivAt (f p) (f' p x) x)
    (hfc : ContinuousAt (fun z : P × X => f z.1 z.2) (p0, x0))
    (hf'c : ContinuousAt (fun z : P × X => f' z.1 z.2) (p0, x0))
    (hsol : -(f p0 x0) ∈ normalCone C x0)
    (lam : ℝ) (hreg : StronglyRegular C (f p0 x0) (f' p0 x0) x0 lam) :
    ∀ eps > 0, ∃ N ∈ 𝓝 p0, ∃ W ∈ 𝓝 x0, W ⊆ Ω ∧ ∃ x : P → X,
      (∀ p ∈ N, x p ∈ W ∧ -(f p (x p)) ∈ normalCone C (x p) ∧
          ∀ z ∈ W, -(f p z) ∈ normalCone C z → z = x p) ∧
      ∀ p ∈ N, ∀ q ∈ N, ‖x p - x q‖ ≤ (lam + eps) * ‖f p (x q) - f q (x q)‖ := by
  intro eps heps
  obtain ⟨U, hU, V, hV, s, hs, hsL⟩ := hreg
  obtain ⟨L, hLdef⟩ : ∃ L, L = max lam 0 := ⟨_, rfl⟩
  have hL0 : 0 ≤ L := hLdef ▸ le_max_right _ _
  have hlamL : lam ≤ L := hLdef ▸ le_max_left _ _
  -- choice of delta
  obtain ⟨δ, hδ0, hκ1, hκeps⟩ : ∃ δ > 0, L * δ < 1 ∧ L * δ * (lam + eps) ≤ eps := by
    have hD : 0 < 2 * (L + 1) * (L + eps + 1) := by positivity
    refine ⟨eps / (2 * (L + 1) * (L + eps + 1)), by positivity, ?_, ?_⟩
    · rw [← mul_div_assoc, div_lt_one hD]; nlinarith
    · have h1 : L * (eps / (2 * (L + 1) * (L + eps + 1))) * (lam + eps) ≤
          L * (eps / (2 * (L + 1) * (L + eps + 1))) * (L + eps) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      refine h1.trans ?_
      rw [← mul_div_assoc, div_mul_eq_mul_div, div_le_iff₀ hD]
      nlinarith [mul_nonneg hL0 heps.le, mul_nonneg (mul_nonneg hL0 heps.le) heps.le]
  -- sigma
  obtain ⟨σ, hσ0, hσU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hU
  set U' := Metric.closedBall (0 : StrongDual ℝ X) σ with hU'def
  have hs' : ∀ y ∈ U', s y ∈ V ∧ y - (f p0 x0 + f' p0 x0 (s y - x0)) ∈ normalCone C (s y) ∧
      ∀ z ∈ V, y - (f p0 x0 + f' p0 x0 (z - x0)) ∈ normalCone C z → z = s y :=
    fun y hy => hs y (hσU hy)
  have hsL' : ∀ y₁ ∈ U', ∀ y₂ ∈ U', ‖s y₁ - s y₂‖ ≤ L * ‖y₁ - y₂‖ := fun y₁ h₁ y₂ h₂ =>
    (hsL y₁ (hσU h₁) y₂ (hσU h₂)).trans (mul_le_mul_of_nonneg_right hlamL (norm_nonneg _))
  have hU'0 : (0 : StrongDual ℝ X) ∈ U' := Metric.mem_closedBall_self hσ0.le
  -- joint continuity
  have h1 : ∀ᶠ z in 𝓝 (p0, x0), ‖f' z.1 z.2 - f' p0 x0‖ ≤ δ := by
    have h' : Filter.Tendsto (fun z : P × X => f' z.1 z.2) (𝓝 (p0, x0))
        (@nhds _ (inferInstance : PseudoMetricSpace
          (X →L[ℝ] StrongDual ℝ X)).toUniformSpace.toTopologicalSpace (f' p0 x0)) := hf'c
    filter_upwards [Metric.tendsto_nhds.mp h' δ hδ0] with z hz
    exact (calc ‖f' z.1 z.2 - f' p0 x0‖ = dist (f' z.1 z.2) (f' p0 x0) :=
        (dist_eq_norm (f' z.1 z.2) (f' p0 x0)).symm
      _ < δ := hz).le
  have h2 : ∀ᶠ z in 𝓝 (p0, x0), ‖residual f f' p0 x0 z.1 z.2‖ ≤ σ := by
    have hc : ContinuousAt (fun z : P × X => f p0 x0 + f' p0 x0 (z.2 - x0) - f z.1 z.2)
        (p0, x0) :=
      (continuousAt_const.add ((f' p0 x0).continuous.continuousAt.comp
        (continuousAt_snd.sub continuousAt_const))).sub hfc
    have h0 : (fun z : P × X => f p0 x0 + f' p0 x0 (z.2 - x0) - f z.1 z.2) (p0, x0) = 0 := by
      simp
    have := hc.eventually (Metric.closedBall_mem_nhds _ hσ0)
    rw [h0] at this
    filter_upwards [this] with z hz
    rw [dist_zero_right] at hz
    exact hz
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.mp (h1.and h2)
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (Filter.inter_mem (Filter.inter_mem hv hV) (hΩ.mem_nhds hx0))
  set B := Metric.closedBall x0 ρ with hBdef
  have hx0B : x0 ∈ B := Metric.mem_closedBall_self hρ.le
  have hball : B ⊆ V ∩ Ω := fun z hz => ⟨(hρsub hz).1.2, (hρsub hz).2⟩
  have hBΩ : B ⊆ Ω := fun z hz => (hρsub hz).2
  -- continuity in p
  have hτ : 0 < (1 - L * δ) * ρ / (L + 1) := by
    have : 0 < 1 - L * δ := by linarith
    positivity
  have h3 : ∀ᶠ p in 𝓝 p0, dist (f p x0) (f p0 x0) < (1 - L * δ) * ρ / (L + 1) := by
    have hc : ContinuousAt (fun p : P => f p x0) p0 :=
      hfc.comp (f := fun p : P => (p, x0)) (continuous_id.prodMk continuous_const).continuousAt
    exact Metric.tendsto_nhds.mp hc _ hτ
  set N := u ∩ {p | dist (f p x0) (f p0 x0) < (1 - L * δ) * ρ / (L + 1)} with hNdef
  have hNmem : N ∈ 𝓝 p0 := Filter.inter_mem hu h3
  -- per-p facts
  have hUp : ∀ p ∈ N, ∀ x ∈ B, residual f f' p0 x0 p x ∈ U' := by
    intro p hp x hx
    have := (huv (Set.mk_mem_prod hp.1 (hρsub hx).1.1)).2
    rw [hU'def, Metric.mem_closedBall, dist_zero_right]
    exact this
  have hdp : ∀ p ∈ N, ∀ x ∈ B, ‖f' p x - f' p0 x0‖ ≤ δ := by
    intro p hp x hx
    exact (huv (Set.mk_mem_prod hp.1 (hρsub hx).1.1)).1
  have hNp : ∀ p ∈ N, L * ‖f p0 x0 - f p x0‖ ≤ (1 - L * δ) * ρ := by
    intro p hp
    have hd := hp.2
    simp only [Set.mem_setOf_eq, dist_eq_norm] at hd
    rw [norm_sub_rev] at hd
    have hk : 0 < 1 - L * δ := by linarith
    have : L * ‖f p0 x0 - f p x0‖ ≤ L * ((1 - L * δ) * ρ / (L + 1)) :=
      mul_le_mul_of_nonneg_left hd.le hL0
    refine this.trans ?_
    rw [mul_div_assoc', div_le_iff₀ (by linarith)]
    nlinarith [mul_pos hk hρ]
  have key : ∀ p ∈ N, ∃ xp ∈ B, s (residual f f' p0 x0 p xp) = xp ∧
      (∀ z ∈ B, s (residual f f' p0 x0 p z) = z → z = xp) ∧
      ∀ x ∈ B, ‖xp - x‖ ≤ (1 - L * δ)⁻¹ *
        ‖s (residual f f' p0 x0 p x) - x‖ := by
    intro p hp
    have hself := sm_core C Ω p0 x0 f f' hf' hsol U' V s hs' hU'0 L hL0 hsL' ρ δ hρ hδ0 hκ1
      hball p (hUp p hp) (hdp p hp) (hNp p hp)
    have hcon := ce_core Ω p0 x0 f f' hf' U' s L hL0 hsL' ρ δ hδ0 hBΩ p (hUp p hp) (hdp p hp)
    have hrl := rlip_core Ω p0 x0 f f' hf' ρ δ hBΩ p (hdp p hp)
    have hLip : LipschitzOnWith (Real.toNNReal L) s U' := by
      refine LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_
      rw [Real.coe_toNNReal _ hL0, dist_eq_norm, dist_eq_norm]
      exact hsL' a ha b hb
    have hDc : IsClosed (U' ∩ s ⁻¹' B) :=
      hLip.continuousOn.preimage_isClosed_of_isClosed Metric.isClosed_closedBall
        Metric.isClosed_closedBall
    have hmaps : Set.MapsTo (fun y => residual f f' p0 x0 p (s y)) (U' ∩ s ⁻¹' B)
        (U' ∩ s ⁻¹' B) := fun y hy => ⟨hUp p hp _ hy.2, hself _ hy.2⟩
    obtain ⟨ys, hys, hysf⟩ := cp_gen_core (U' ∩ s ⁻¹' B) hDc.isComplete
      (residual f f' p0 x0 p x0) ⟨hUp p hp _ hx0B, hself _ hx0B⟩ _ hmaps (δ * L)
      (mul_nonneg hδ0.le hL0) (by linarith [mul_comm L δ]) (by
        intro y₁ h₁ y₂ h₂
        rw [dist_eq_norm, dist_eq_norm]
        calc _ ≤ δ * ‖s y₁ - s y₂‖ := hrl _ h₁.2 _ h₂.2
          _ ≤ δ * (L * ‖y₁ - y₂‖) := mul_le_mul_of_nonneg_left (hsL' _ h₁.1 _ h₂.1) hδ0.le
          _ = _ := by ring)
    have hfix : s (residual f f' p0 x0 p (s ys)) = s ys := by
      exact congrArg s hysf
    have hub := ub_core B (fun x => s (residual f f' p0 x0 p x)) (L * δ) hκ1
      hcon (s ys) hys.2 hfix
    exact ⟨s ys, hys.2, hfix, hub.1, hub.2⟩
  have key' : ∀ p, ∃ xp : X, p ∈ N → (xp ∈ B ∧ s (residual f f' p0 x0 p xp) = xp ∧
      (∀ z ∈ B, s (residual f f' p0 x0 p z) = z → z = xp) ∧
      ∀ x ∈ B, ‖xp - x‖ ≤ (1 - L * δ)⁻¹ * ‖s (residual f f' p0 x0 p x) - x‖) := by
    intro p
    by_cases hp : p ∈ N
    · obtain ⟨xp, h1, h2, h3, h4⟩ := key p hp
      exact ⟨xp, fun _ => ⟨h1, h2, h3, h4⟩⟩
    · exact ⟨x0, fun h => absurd h hp⟩
  choose x hx using key'
  have hfps : ∀ p ∈ N, ∀ z ∈ B,
      (s (residual f f' p0 x0 p z) = z ↔ -(f p z) ∈ normalCone C z) := fun p hp =>
    fps_core C p0 x0 f f' U' V s hs' ρ (fun z hz => (hball hz).1) p (hUp p hp)
  refine ⟨N, hNmem, B, Metric.closedBall_mem_nhds x0 hρ, hBΩ, x, ?_, ?_⟩
  · intro p hp
    obtain ⟨hxB, hfix, huniq, -⟩ := hx p hp
    exact ⟨hxB, (hfps p hp _ hxB).mp hfix,
      fun z hz hzs => huniq z hz ((hfps p hp z hz).mpr hzs)⟩
  · intro p hp q hq
    obtain ⟨hqB, hqfix, -, -⟩ := hx q hq
    have hb := (hx p hp).2.2.2 (x q) hqB
    have hl := hsL _ (hσU (hUp p hp _ hqB)) _ (hσU (hUp q hq _ hqB))
    have hreq : residual f f' p0 x0 p (x q) - residual f f' p0 x0 q (x q) =
        f q (x q) - f p (x q) := by unfold residual; abel
    rw [hreq, hqfix, norm_sub_rev (f q (x q))] at hl
    have hk : 0 < 1 - L * δ := by linarith
    have hcoef : (1 - L * δ)⁻¹ * lam ≤ lam + eps := by
      rw [inv_mul_le_iff₀ hk]; nlinarith
    calc ‖x p - x q‖ ≤ (1 - L * δ)⁻¹ * (lam * ‖f p (x q) - f q (x q)‖) :=
          hb.trans (mul_le_mul_of_nonneg_left hl (inv_nonneg.mpr hk.le))
      _ = ((1 - L * δ)⁻¹ * lam) * ‖f p (x q) - f q (x q)‖ := by ring
      _ ≤ (lam + eps) * ‖f p (x q) - f q (x q)‖ :=
          mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)

end RobinsonSR.IFT

open RobinsonSR.IFT
open scoped Topology

theorem solution {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (C : Set X) (hC : IsClosed C) (hCc : Convex ℝ C)
    (Ω : Set X) (hΩ : IsOpen Ω) (x0 : X) (hx0 : x0 ∈ Ω)
    {P : Type*} [TopologicalSpace P] (p0 : P)
    (f : P → X → StrongDual ℝ X) (f' : P → X → (X →L[ℝ] StrongDual ℝ X))
    (hf' : ∀ p, ∀ x ∈ Ω, HasFDerivAt (f p) (f' p x) x)
    (hfc : ContinuousAt (fun z : P × X => f z.1 z.2) (p0, x0))
    (hf'c : ContinuousAt (fun z : P × X => f' z.1 z.2) (p0, x0))
    (hsol : -(f p0 x0) ∈ normalCone C x0)
    (lam : ℝ) (hreg : StronglyRegular C (f p0 x0) (f' p0 x0) x0 lam) :
    ∀ eps > 0, ∃ N ∈ 𝓝 p0, ∃ W ∈ 𝓝 x0, W ⊆ Ω ∧ ∃ x : P → X,
      (∀ p ∈ N, x p ∈ W ∧ -(f p (x p)) ∈ normalCone C (x p) ∧
          ∀ z ∈ W, -(f p z) ∈ normalCone C z → z = x p) ∧
      ∀ p ∈ N, ∀ q ∈ N, ‖x p - x q‖ ≤ (lam + eps) * ‖f p (x q) - f q (x q)‖ := by
  exact t21_core C hC hCc Ω hΩ x0 hx0 p0 f f' hf' hfc hf'c hsol lam hreg

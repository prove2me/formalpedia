-- Prove2me | solution 1 for PHarmJetTailEstimate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:22:14.700612+00:00
-- url     : https://prove2.me/submissions/6b3807ad-776d-4a99-a9d7-ebef107d781c

import Definitions.Def_PHigherOrder_PHarmJetEquicontinuity
import Definitions.Def_PHigherOrder_PHarmRestrict
import Definitions.Def_PHigherOrder_PHarmJetTailEstimate
import Theorems.Thm_PHarmJetEquicontinuity
import Theorems.Thm_PHarmRestrict


set_option autoImplicit false

theorem _root_.solution (p : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (F : FirstOrderEstimateInput p)
    (Ω : ℕ → Set Plane) (hmono : Monotone Ω)
    (v : ℕ → Plane → ℝ) (g : ℕ → Plane → Plane)
    (hph : ∀ n : ℕ, IsPHarm p (Ω n) (v n) (g n))
    (hbd : ∀ K : Set Plane, K ⊆ (⋃ n, Ω n) → IsCompact K →
        ∃ M : ℝ, 0 < M ∧ ∃ N : ℕ, ∀ n, N ≤ n → ∀ z ∈ K, |v n z| ≤ M)
    (K : Set Plane) (hK : K ⊆ (⋃ n, Ω n)) (hKc : IsCompact K) :
    ∃ (N : ℕ) (A L R : ℝ), 0 < A ∧ 0 < L ∧ 0 < R ∧ ∀ n, N ≤ n →
      ContinuousOn (v n) K ∧ ContinuousOn (fun z => gradient (v n) z) K ∧
      (∀ z ∈ K, |v n z| ≤ A) ∧
      (∀ z ∈ K, ‖gradient (v n) z‖ ≤ L) ∧
      (∀ z ∈ K, ∀ z' ∈ K, ‖z - z'‖ < 3 * R / 4 →
        ‖gradient (v n) z - gradient (v n) z'‖ ≤ L * (‖z - z'‖ / (2 * R)) ^ F.kappa) ∧
      (∀ z ∈ K, ∀ z' ∈ K, ‖z - z'‖ < 3 * R / 4 → |v n z - v n z'| ≤ L * ‖z - z'‖) := by
  have hopen : ∀ n : ℕ, IsOpen (Ω n) := fun n => (hph n).openOmega
  have hWopen : IsOpen (⋃ n, Ω n) := isOpen_iUnion hopen
  -- Step 3a: thicken `K` to buy room for the doubled ball.
  obtain ⟨ρ, hρ, hρsub⟩ := hKc.exists_cthickening_subset_open hWopen hK
  have hKρc : IsCompact (Metric.cthickening ρ K) := hKc.cthickening
  -- Step 1: the thickened compact lies in a single domain, hence in all later ones.
  obtain ⟨N₁, hN₁⟩ := hKρc.elim_directed_cover Ω hopen hρsub hmono.directed_le
  -- Step 3b: a uniform bound on the thickened compact, along a tail.
  obtain ⟨A, hA, N₂, hN₂⟩ := hbd (Metric.cthickening ρ K) hρsub hKρc
  -- The constants are produced here, BEFORE any index is fixed.
  have hR : (0 : ℝ) < ρ / 4 := by positivity
  have hL : (0 : ℝ) < F.C₀ * A / (2 * (ρ / 4)) := by
    have := F.C₀_pos
    positivity
  refine ⟨max N₁ N₂, A, F.C₀ * A / (2 * (ρ / 4)), ρ / 4, hA, hL, hR, ?_⟩
  intro n hn
  have hn1 : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : N₂ ≤ n := le_trans (le_max_right _ _) hn
  have hΩsub : Metric.cthickening ρ K ⊆ Ω n := hN₁.trans (hmono hn1)
  -- Step 3c: the one-ball estimate at every centre of `K`, with these constants.
  have hjet : ∀ z₀ ∈ K,
      ContDiffOn ℝ 1 (v n) (Metric.ball z₀ (3 * (ρ / 4) / 2)) ∧
      (∀ z ∈ Metric.ball z₀ (3 * (ρ / 4) / 2),
        ‖gradient (v n) z‖ ≤ F.C₀ * A / (2 * (ρ / 4))) ∧
      (∀ z ∈ Metric.ball z₀ (3 * (ρ / 4) / 2), ∀ z' ∈ Metric.ball z₀ (3 * (ρ / 4) / 2),
        ‖gradient (v n) z - gradient (v n) z'‖
          ≤ F.C₀ * A / (2 * (ρ / 4)) * (‖z - z'‖ / (2 * (ρ / 4))) ^ F.kappa) := by
    intro z₀ hz₀
    have hballsub : Metric.ball z₀ (2 * (ρ / 4)) ⊆ Metric.cthickening ρ K := by
      have h1 : Metric.ball z₀ (2 * (ρ / 4)) ⊆ Metric.closedBall z₀ ρ := by
        intro y hy
        simp only [Metric.mem_ball] at hy
        simp only [Metric.mem_closedBall]
        linarith
      exact h1.trans (Metric.closedBall_subset_cthickening hz₀ ρ)
    have hbnd : ∀ z ∈ Metric.ball z₀ (2 * (ρ / 4)), |v n z| ≤ A := fun z hz =>
      hN₂ n hn2 z (hballsub hz)
    have hpharm : IsPHarm p (Metric.ball z₀ (2 * (ρ / 4))) (v n) (g n) :=
      (PHarmRestrict p hp hp2 (Ω n) (v n) (g n) (hph n)).1 _ Metric.isOpen_ball
        (hballsub.trans hΩsub)
    exact PHarmJetEquicontinuity p hp hp2 F z₀ (ρ / 4) A hR hA (v n) (g n) hpharm hbnd
  -- Each point of `K` is the centre of such a ball, which gives (i), and taking the centre
  -- to be the point itself gives the pointwise and nearby-pair bounds (ii)--(iv).
  have hself : ∀ z ∈ K, z ∈ Metric.ball z (3 * (ρ / 4) / 2) :=
    fun z _ => Metric.mem_ball_self (by linarith)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (i) continuity of `v n` on `K`
    intro z hz
    refine ContinuousAt.continuousWithinAt ?_
    refine ((hjet z hz).1.continuousOn.continuousAt ?_)
    exact Metric.isOpen_ball.mem_nhds (hself z hz)
  · -- (i) continuity of the gradient on `K`
    intro z hz
    refine ContinuousAt.continuousWithinAt ?_
    have hcg : ContinuousOn (fun y => gradient (v n) y) (Metric.ball z (3 * (ρ / 4) / 2)) :=
      (InnerProductSpace.toDual ℝ Plane).symm.continuous.comp_continuousOn
        ((hjet z hz).1.continuousOn_fderiv_of_isOpen Metric.isOpen_ball le_rfl)
    exact hcg.continuousAt (Metric.isOpen_ball.mem_nhds (hself z hz))
  · -- (ii) the bound on `v n`
    exact fun z hz => hN₂ n hn2 z (Metric.self_subset_cthickening K hz)
  · -- (ii) the bound on the gradient
    exact fun z hz => (hjet z hz).2.1 z (hself z hz)
  · -- (iii) the Holder bound for nearby pairs
    intro z hz z' hz' hd
    refine (hjet z hz).2.2 z (hself z hz) z' ?_
    simp only [Metric.mem_ball, dist_eq_norm]
    calc ‖z' - z‖ = ‖z - z'‖ := by rw [norm_sub_rev]
      _ < 3 * (ρ / 4) / 4 := hd
      _ < 3 * (ρ / 4) / 2 := by linarith
  · -- (iv) the Lipschitz bound for nearby pairs, by the mean value inequality
    intro z hz z' hz' hd
    have hz'mem : z' ∈ Metric.ball z (3 * (ρ / 4) / 2) := by
      simp only [Metric.mem_ball, dist_eq_norm]
      calc ‖z' - z‖ = ‖z - z'‖ := by rw [norm_sub_rev]
        _ < 3 * (ρ / 4) / 4 := hd
        _ < 3 * (ρ / 4) / 2 := by linarith
    have hC := (hjet z hz).1
    have hdiff : ∀ x ∈ Metric.ball z (3 * (ρ / 4) / 2), DifferentiableAt ℝ (v n) x := by
      intro x hx
      exact ((hC.differentiableOn one_ne_zero) x hx).differentiableAt
        (Metric.isOpen_ball.mem_nhds hx)
    have hnb : ∀ x ∈ Metric.ball z (3 * (ρ / 4) / 2),
        ‖fderiv ℝ (v n) x‖ ≤ F.C₀ * A / (2 * (ρ / 4)) := by
      intro x hx
      have heq : ‖gradient (v n) x‖ = ‖fderiv ℝ (v n) x‖ := by
        rw [← toDual_gradient (𝕜 := ℝ) (f := v n) (x := x)]
        exact ((InnerProductSpace.toDual ℝ Plane).norm_map _).symm
      rw [← heq]
      exact (hjet z hz).2.1 x hx
    have hmv := (convex_ball z (3 * (ρ / 4) / 2)).norm_image_sub_le_of_norm_fderiv_le
      hdiff hnb hz'mem (hself z hz)
    rwa [Real.norm_eq_abs] at hmv

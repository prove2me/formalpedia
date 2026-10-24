-- Prove2me | solution 1 for ShorNonsmooth.Fejer.fejer_map_iterates_converge
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-23T11:10:32.46606+00:00
-- url     : https://prove2.me/submissions/9ea84553-a1c3-4d8e-9f96-c2f9655b5184

import Definitions.Def_ShorNonsmooth_Fejer_PolyakMethod

open Filter Topology
open ShorNonsmooth.Fejer

set_option maxHeartbeats 800000

/-- Continuous strict Fejer maps have convergent orbits in finite-dimensional space. -/
theorem solution {n : ℕ} (M : Set (EuclideanSpace ℝ (Fin n)))
    (φ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hφ : IsMFejer M φ) (hcont : Continuous φ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (hx : ∀ k, x (k + 1) = φ (x k)) :
    ∃ xbar ∈ M, Tendsto x atTop (𝓝 xbar) := by
  have hanti : ∀ y ∈ M, Antitone (fun k => ‖x k - y‖) := by
    intro y hy
    apply antitone_nat_of_succ_le
    intro k
    rw [hx k]
    by_cases hk : x k ∈ M
    · rw [hφ.2.1 _ hk]
    · exact (hφ.2.2 y hy (x k) hk).le
  obtain ⟨y, hy⟩ := hφ.1
  obtain ⟨a, _, r, hr, ha⟩ := tendsto_subseq_of_bounded
    (Metric.isBounded_closedBall (x := y) (r := ‖x 0 - y‖))
    (x := x) (fun k => by
      rw [Metric.mem_closedBall, dist_eq_norm]
      exact hanti y hy (Nat.zero_le k))
  have hlim : Tendsto (fun k => ‖x k - y‖) atTop (𝓝 ‖a - y‖) :=
    (tendsto_iff_tendsto_subseq_of_antitone (hanti y hy) hr.tendsto_atTop).mpr
      ((ha.sub_const y).norm)
  have hshift : Tendsto (fun k => ‖x (r k + 1) - y‖) atTop (𝓝 ‖a - y‖) :=
    hlim.comp ((tendsto_add_atTop_nat 1).comp hr.tendsto_atTop)
  have hmap : Tendsto (fun k => ‖x (r k + 1) - y‖) atTop (𝓝 ‖φ a - y‖) := by
    simp_rw [hx]
    exact ((hcont.tendsto a |>.comp ha).sub_const y).norm
  have ham : a ∈ M := by
    by_contra hn
    have heq := tendsto_nhds_unique hmap hshift
    exact (ne_of_lt (hφ.2.2 y hy a hn)) heq
  refine ⟨a, ham, ?_⟩
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact (tendsto_iff_tendsto_subseq_of_antitone (hanti a ham) hr.tendsto_atTop).mpr
    (by simpa only [Function.comp_def, sub_self, norm_zero] using (ha.sub_const a).norm)



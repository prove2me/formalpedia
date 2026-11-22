-- Prove2me | solution 1 for ZeroOneIALM.isolated_clusterPt_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-21T09:15:16.99681+00:00
-- url     : https://prove2.me/submissions/45b0d32a-1008-4068-b813-11145e8373c1

import Mathlib

open Filter Topology

theorem solution {X : Type*} [MetricSpace X] [ProperSpace X]
    {x : ℕ → X} {xstar : X}
    (hstep : Tendsto (fun k => dist (x (k + 1)) (x k)) atTop (𝓝 0))
    (hcluster : MapClusterPt xstar atTop x)
    (hisolated : ∃ δ : ℝ, 0 < δ ∧ ∀ y, MapClusterPt y atTop x → dist y xstar < δ → y = xstar) :
    Tendsto x atTop (𝓝 xstar) := by
  classical
  obtain ⟨δ, hδpos, hδiso⟩ := hisolated
  rw [Metric.tendsto_atTop]
  intro ε₀ hε₀
  by_contra hcon
  push_neg at hcon
  let ε := min (ε₀ / 2) (δ / 4)
  have hεpos : 0 < ε := lt_min (by linarith) (by linarith)
  have hεδ : 2 * ε < δ := by
    have := min_le_right (ε₀ / 2) (δ / 4)
    linarith
  have hεε₀ : 2 * ε ≤ ε₀ := by
    have := min_le_left (ε₀ / 2) (δ / 4)
    linarith
  -- eventually the steps are smaller than `ε`
  have hstepev : ∀ᶠ k in atTop, dist (x (k + 1)) (x k) < ε := by
    obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.mp hstep) ε hεpos
    filter_upwards [eventually_ge_atTop N₀] with k hk
    have h := hN₀ k hk
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg] at h
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hstepev
  -- frequently far away
  have hout : ∃ᶠ k in atTop, 2 * ε ≤ dist (x k) xstar := by
    rw [frequently_atTop]
    intro N
    obtain ⟨n, hnN, hnd⟩ := hcon N
    exact ⟨n, hnN, le_trans hεε₀ hnd⟩
  -- frequently close
  have hin : ∃ᶠ k in atTop, dist (x k) xstar < ε := by
    have hmem : Metric.ball xstar ε ∈ 𝓝 xstar := Metric.ball_mem_nhds xstar hεpos
    have h := (mapClusterPt_iff_frequently.mp hcluster) (Metric.ball xstar ε) hmem
    simpa [Metric.mem_ball] using h
  -- the annulus
  let A : Set X := {y | ε ≤ dist y xstar ∧ dist y xstar ≤ 2 * ε}
  have hfreqA : ∃ᶠ m in atTop, x m ∈ A := by
    rw [frequently_atTop]
    intro N
    obtain ⟨k', hk'ge, hk'd⟩ := (frequently_atTop.mp hout) (max N N₁)
    obtain ⟨k'', hk''ge, hk''d⟩ := (frequently_atTop.mp hin) k'
    have hex : ∃ m, k' ≤ m ∧ dist (x m) xstar ≤ 2 * ε :=
      ⟨k'', hk''ge, le_of_lt (lt_of_lt_of_le hk''d (by linarith))⟩
    let m := Nat.find hex
    have hmspec : k' ≤ m ∧ dist (x m) xstar ≤ 2 * ε := Nat.find_spec hex
    refine ⟨m, ?_, ?_, hmspec.2⟩
    · exact le_trans (le_max_left N N₁) (le_trans hk'ge hmspec.1)
    · by_cases hmk : m = k'
      · rw [hmk]
        linarith
      · have hmlt : k' < m := lt_of_le_of_ne hmspec.1 (Ne.symm hmk)
        have hprev : 2 * ε < dist (x (m - 1)) xstar := by
          have hmin := Nat.find_min hex (show m - 1 < m by omega)
          have hk'le : k' ≤ m - 1 := by omega
          by_contra hle
          push_neg at hle
          exact hmin ⟨hk'le, hle⟩
        have hstepm : dist (x m) (x (m - 1)) < ε := by
          have hN0 : N₁ ≤ m - 1 := by omega
          have h := hN₁ (m - 1) hN0
          rwa [show m - 1 + 1 = m by omega] at h
        have hsym : dist (x (m - 1)) (x m) < ε := by rwa [dist_comm]
        have htri : dist (x (m - 1)) xstar ≤ dist (x (m - 1)) (x m) + dist (x m) xstar :=
          dist_triangle _ _ _
        linarith
  -- compactness of the annulus
  have hAcompact : IsCompact A := by
    rw [Metric.isCompact_iff_isClosed_bounded]
    have hAeq : A = {y : X | ε ≤ dist y xstar} ∩ Metric.closedBall xstar (2 * ε) := by
      ext y
      rfl
    refine ⟨?_, ?_⟩
    · rw [hAeq]
      exact (isClosed_le continuous_const (continuous_id.dist continuous_const)).inter
        Metric.isClosed_closedBall
    · rw [hAeq]
      exact Metric.isBounded_closedBall.subset Set.inter_subset_right
  obtain ⟨y, hyA, φ, hφmono, hφtend⟩ := IsCompact.tendsto_subseq' hAcompact hfreqA
  -- `y` is a cluster point of the whole sequence
  have hφat : Tendsto φ atTop atTop := hφmono.tendsto_atTop
  have hle : map (x ∘ φ) atTop ≤ map x atTop := by
    rw [← map_map]
    exact map_mono hφat
  have hcl : MapClusterPt y atTop x := by
    have h1 : ClusterPt y (map (x ∘ φ) atTop) := ClusterPt.of_le_nhds hφtend
    exact ClusterPt.mono h1 hle
  -- contradiction with isolation
  have hyδ : dist y xstar < δ := lt_of_le_of_lt hyA.2 (by linarith)
  have hyeq : y = xstar := hδiso y hcl hyδ
  have hzero : dist y xstar = 0 := by rw [hyeq, dist_self]
  linarith [hyA.1]


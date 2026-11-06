-- Prove2me | solution 1 for WhittFLT.FirstPassage.m1_tendsto_continuous_imp_u
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T02:38:23.700682+00:00
-- url     : https://prove2.me/submissions/3ebc5c9f-0a80-4b64-8f57-4f07a2f027ba

import Mathlib
import Definitions.Def_WhittFLT_FirstPassage_M1

open WhittFLT.FirstPassage

open Set Filter Topology

theorem solution (xs : ℕ → ℝ → ℝ) (x : ℝ → ℝ)
    (h : M1Tendsto xs x) (hc : ContinuousOn x (Ici 0)) (h0 : x 0 = 0) :
    WhittFLT.Composition.UTendsto (Ici 0) xs x := by
  intro a b hab
  set B : ℝ := max b 1 with hB
  have hBpos : 0 < B := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hcB : ContinuousAt x B :=
    hc.continuousAt (Ici_mem_nhds hBpos)
  have hM := h.2.2 B hBpos hcB
  -- uniform continuity on [0, B]
  have hUC : UniformContinuousOn x (Icc 0 B) :=
    isCompact_Icc.uniformContinuousOn_of_continuous (hc.mono Icc_subset_Ici_self)
  rw [Metric.uniformContinuousOn_iff] at hUC
  -- left limits agree with values for the continuous limit
  have hll : ∀ t ∈ Icc (0:ℝ) B, leftLim0 x t = x t := by
    intro t ht
    unfold leftLim0
    split_ifs with h1
    · rw [h1, h0]
    · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm h1)
      have hct : ContinuousAt x t := hc.continuousAt (Ici_mem_nhds htpos)
      exact leftLim_eq_of_tendsto (hct.tendsto.mono_left nhdsWithin_le_nhds)
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  -- reduce to a real δ
  obtain ⟨δ, hδpos, hδe⟩ : ∃ δ : ℝ, 0 < δ ∧ ENNReal.ofReal δ ≤ e := by
    rcases eq_or_ne e ⊤ with rfl | hne
    · exact ⟨1, one_pos, le_top⟩
    · refine ⟨e.toReal, ENNReal.toReal_pos he.ne' hne, ?_⟩
      rw [ENNReal.ofReal_toReal hne]
  obtain ⟨η, hηpos, hη⟩ := hUC (δ / 2) (by linarith)
  have hε : 0 < min η (δ / 2) := lt_min hηpos (by linarith)
  filter_upwards [hM _ hε] with n hn
  obtain ⟨r', u', r, u, hrep', hrep, hclose⟩ := hn
  refine le_trans ?_ hδe
  unfold WhittFLT.Composition.supDist
  refine iSup₂_le fun t ht => ?_
  have ht0 : t ∈ Icc (0:ℝ) B := ⟨hab ht, le_trans ht.2 (le_max_left _ _)⟩
  have hmem : (t, xs n t) ∈ completedGraph B (xs n) :=
    ⟨ht0, 0, ⟨le_refl _, zero_le_one⟩, by ring⟩
  rw [← hrep'.2.2.1] at hmem
  obtain ⟨s, hs, hseq⟩ := hmem
  simp only [Prod.mk.injEq] at hseq
  obtain ⟨hrs', hus'⟩ := hseq
  have hmemx : (r s, u s) ∈ completedGraph B x := by
    rw [← hrep.2.2.1]; exact ⟨s, hs, rfl⟩
  obtain ⟨hrsI, α, hα, hus⟩ := hmemx
  simp only at hrsI hus
  rw [hll _ hrsI] at hus
  have hux : u s = x (r s) := by rw [hus]; ring
  obtain ⟨hc1, hc2⟩ := hclose s hs
  rw [hrs'] at hc2
  rw [hus'] at hc1
  have hd : dist (x (r s)) (x t) < δ / 2 := by
    apply hη _ hrsI _ ht0
    rw [Real.dist_eq, abs_sub_comm]
    exact lt_of_lt_of_le hc2 (min_le_left _ _)
  rw [Real.dist_eq] at hd
  rw [hux] at hc1
  rw [edist_dist, Real.dist_eq]
  apply ENNReal.ofReal_le_ofReal
  have := min_le_right η (δ / 2)
  calc |xs n t - x t| ≤ |xs n t - x (r s)| + |x (r s) - x t| := abs_sub_le _ _ _
    _ ≤ δ := by linarith


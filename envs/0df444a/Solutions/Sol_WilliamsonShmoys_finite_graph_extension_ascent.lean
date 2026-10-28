-- Prove2me | solution 1 for WilliamsonShmoys.finite_graph_extension_ascent
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T18:17:55.1095+00:00
-- url     : https://prove2.me/submissions/7d7eea2d-c50d-44b0-9b7c-de2d6be783b0

import Mathlib

theorem solution {V : Type} [Fintype V] (K : SimpleGraph V) (P : SimpleGraph V → Prop) (hP : P K) (hstep : ∀ (L : SimpleGraph V), K ≤ L → P L → ¬ L.Connected → ∃ M : SimpleGraph V, L ≤ M ∧ P M ∧ L.edgeSet.ncard < M.edgeSet.ncard) : ∃ L : SimpleGraph V, K ≤ L ∧ L.Connected ∧ P L ∧ K.edgeSet.ncard ≤ L.edgeSet.ncard := by
  obtain ⟨L, ⟨hKL, hPL⟩, hmax⟩ := Set.exists_max_image {G : SimpleGraph V | K ≤ G ∧ P G}
    (fun G => G.edgeSet.ncard) (Set.toFinite _) ⟨K, le_rfl, hP⟩
  by_cases hc : L.Connected
  · exact ⟨L, hKL, hc, hPL, Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hKL) (Set.toFinite _)⟩
  · obtain ⟨M, hLM, hPM, hlt⟩ := hstep L hKL hPL hc
    have := hmax M ⟨le_trans hKL hLM, hPM⟩
    omega

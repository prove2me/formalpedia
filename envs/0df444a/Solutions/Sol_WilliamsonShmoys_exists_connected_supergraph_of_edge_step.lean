-- Prove2me | solution 1 for WilliamsonShmoys.exists_connected_supergraph_of_edge_step
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T03:22:39.198245+00:00
-- url     : https://prove2.me/submissions/c05b3bc0-9e86-4aa0-b493-e49cf0fdc64f

import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_connected_supergraph_of_component_decrease
import Theorems.Thm_WilliamsonShmoys_component_count_strictly_decreases_of_cross_edge

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (H : SimpleGraph V)
    (hH : P H)
    (hstep : ∀ G : SimpleGraph V, H ≤ G → P G → ¬ G.Connected →
      ∃ K : SimpleGraph V, G ≤ K ∧ P K ∧
        ∃ u v : V, ¬ G.Reachable u v ∧ K.Adj u v) :
    ∃ K : SimpleGraph V, H ≤ K ∧ K.Connected ∧ P K := by
  apply WilliamsonShmoys.exists_connected_supergraph_of_component_decrease P H hH
  intro G hHG hPG hG
  obtain ⟨K, hGK, hPK, u, v, hnot, hadj⟩ := hstep G hHG hPG hG
  exact ⟨K, hGK, hPK,
    WilliamsonShmoys.component_count_strictly_decreases_of_cross_edge G K hGK u v hnot hadj⟩
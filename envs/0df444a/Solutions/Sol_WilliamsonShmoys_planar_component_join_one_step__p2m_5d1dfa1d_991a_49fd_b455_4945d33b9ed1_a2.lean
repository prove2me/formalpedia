-- Prove2me | solution 1 for WilliamsonShmoys.planar_component_join_one_step__p2m_5d1dfa1d_991a_49fd_b455_4945d33b9ed1_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:05:11.484203+00:00
-- url     : https://prove2.me/submissions/e8b389d5-d8ce-4f44-85ea-32f682ae80cf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_disconnected_bridge_arc__p2m_e5953786_4eb4_4e6c_bc80_19f0610c5350_a2
import Theorems.Thm_WilliamsonShmoys_planar_add_edge_along_bridge_arc__p2m_e5953786_4eb4_4e6c_bc80_19f0610c5350_a2
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (hcard : 3 ≤ Fintype.card V)
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hnot : ¬ G.Connected) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∃ u v : V, ¬ G.Reachable u v ∧ K.Reachable u v := by
  obtain ⟨p, arc, hdraw, hrest⟩ :=
    WilliamsonShmoys.planar_disconnected_bridge_arc__p2m_e5953786_4eb4_4e6c_bc80_19f0610c5350_a2
      hcard G hG hnot
  rcases hrest with ⟨u, v, hu_lt, hrest⟩
  rcases hrest with ⟨hnotreach, c, hc⟩
  have huv : u < v ∧ ¬ G.Reachable u v := ⟨hu_lt, hnotreach⟩
  obtain ⟨K, hsub, hplanar, hreach⟩ :=
    WilliamsonShmoys.planar_add_edge_along_bridge_arc__p2m_e5953786_4eb4_4e6c_bc80_19f0610c5350_a2
      G p arc hdraw u v huv c hc
  exact ⟨K, hsub, hplanar, u, v, hnotreach, hreach⟩
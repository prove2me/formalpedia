-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_planar_graph_has_strict_planar_extension__p2m_76da28cf_203d_4767_b5f5_69763f85c611_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T19:03:18.830754+00:00
-- url     : https://prove2.me/submissions/09ceb606-ebb3-4e89-bcde-ea0ee35cd4d6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_disconnected_graph_has_unreachable_pair__p2m_70e8c091_7bdb_4671_99d7_abbf72db95dd_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_add_edge_for_unreachable_pair__p2m_70e8c091_7bdb_4671_99d7_abbf72db95dd_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hdis : ¬ G.Connected) :
    ∃ H : SimpleGraph V, G < H ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by
  obtain ⟨u, v, hsep⟩ :=
    WilliamsonShmoys.disconnected_graph_has_unreachable_pair__p2m_70e8c091_7bdb_4671_99d7_abbf72db95dd_a1 G hdis
  exact WilliamsonShmoys.planar_drawing_add_edge_for_unreachable_pair__p2m_70e8c091_7bdb_4671_99d7_abbf72db95dd_a1 G hG u v hsep
-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_58a549ee_4768_4664_9403_907071b96f48_a4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T06:16:18.423987+00:00
-- url     : https://prove2.me/submissions/1177d63c-eca3-483c-9186-d5525c8fa162
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound_connected__p2m_5db6a80d_54aa_4e0a_9bf3_96c293216517_a1
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound_induced_local__p2m_5db6a80d_54aa_4e0a_9bf3_96c293216517_a1
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound_components__p2m_5db6a80d_54aa_4e0a_9bf3_96c293216517_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  let hConnectedCore := fun {W : Type} [Fintype W] [LinearOrder W]
      (G : SimpleGraph W) (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
      (hconn : G.Connected) (hn : 3 ≤ Fintype.card W) =>
    WilliamsonShmoys.planar_simple_graph_edge_bound_connected__p2m_5db6a80d_54aa_4e0a_9bf3_96c293216517_a1
      G hG hconn hn
  have hLocal :=
    WilliamsonShmoys.planar_simple_graph_edge_bound_induced_local__p2m_5db6a80d_54aa_4e0a_9bf3_96c293216517_a1
      H hH hConnectedCore
  exact WilliamsonShmoys.planar_simple_graph_edge_bound_components__p2m_5db6a80d_54aa_4e0a_9bf3_96c293216517_a1
    H hLocal hcard

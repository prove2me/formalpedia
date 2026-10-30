-- Prove2me | solution 1 for WilliamsonShmoys.planar_connected_supergraph_of_disconnected_drawing__p2m_b7cc0e50_4117_438e_97b3_add0d92d7fc9_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T18:45:45.586858+00:00
-- url     : https://prove2.me/submissions/16a6a65d-12ef-4d65-ae1f-1082c5acac1f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_extension_principle__p2m_76da28cf_203d_4767_b5f5_69763f85c611_a1
import Theorems.Thm_WilliamsonShmoys_disconnected_planar_graph_has_strict_planar_extension__p2m_76da28cf_203d_4767_b5f5_69763f85c611_a1
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V)
    (hdis : ¬ G.Connected) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ H.Connected ∧ HasPlanarDrawingOn H := by
  apply WilliamsonShmoys.planar_extension_principle__p2m_76da28cf_203d_4767_b5f5_69763f85c611_a1 G hG
  intro H hGH hH hHd
  exact WilliamsonShmoys.disconnected_planar_graph_has_strict_planar_extension__p2m_76da28cf_203d_4767_b5f5_69763f85c611_a1 H hH hHd
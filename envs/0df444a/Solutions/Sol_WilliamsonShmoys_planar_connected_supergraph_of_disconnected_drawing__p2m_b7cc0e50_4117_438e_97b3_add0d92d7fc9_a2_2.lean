-- Prove2me | solution 2 for WilliamsonShmoys.planar_connected_supergraph_of_disconnected_drawing__p2m_b7cc0e50_4117_438e_97b3_add0d92d7fc9_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T20:01:52.972775+00:00
-- url     : https://prove2.me/submissions/2abf3979-9c9d-41e8-b4bd-b1f5a47006fe
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_5852e9a6_6924_436b_b46b_8836657b1500_a1
import Theorems.Thm_WilliamsonShmoys_disconnected_planar_graph_has_strict_planar_extension_of_three_vertices__p2m_76da28cf_203d_4767_b5f5_69763f85c611_a2
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
  obtain ⟨H, hGH, hHplanar, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_5852e9a6_6924_436b_b46b_8836657b1500_a1 G hG
  refine ⟨H, hGH, ?_, hHplanar⟩
  by_contra hHconn
  obtain ⟨K, hHK, hKplanar⟩ :=
    WilliamsonShmoys.disconnected_planar_graph_has_strict_planar_extension_of_three_vertices__p2m_76da28cf_203d_4767_b5f5_69763f85c611_a2
      H hHplanar hV hHconn
  have hKH : K = H := hmax K (le_of_lt hHK) hKplanar
  exact (ne_of_lt hHK) hKH.symm
-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_b387e51f_12e6_457e_b8c7_5aeeed4116ef_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:52:54.291199+00:00
-- url     : https://prove2.me/submissions/0d028a91-931d-4860-934f-7dce44dc29cb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_e546a1c1_10cc_476b_a894_225ced90c5fe_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_simple_graph_edge_count__p2m_e546a1c1_10cc_476b_a894_225ced90c5fe_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hG : HasPlanarDrawingOn G) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hGH, hHplanar, hHmax, hEdges⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension__p2m_e546a1c1_10cc_476b_a894_225ced90c5fe_a1
      G hG
  have hCount :=
    WilliamsonShmoys.maximal_planar_simple_graph_edge_count__p2m_e546a1c1_10cc_476b_a894_225ced90c5fe_a1
      H hV hHplanar hHmax
  omega

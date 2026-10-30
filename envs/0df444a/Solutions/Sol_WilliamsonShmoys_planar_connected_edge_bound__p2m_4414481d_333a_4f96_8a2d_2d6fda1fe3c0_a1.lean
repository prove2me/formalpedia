-- Prove2me | solution 1 for WilliamsonShmoys.planar_connected_edge_bound__p2m_4414481d_333a_4f96_8a2d_2d6fda1fe3c0_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:07:58.767532+00:00
-- url     : https://prove2.me/submissions/24c1ffbf-cfd1-4a35-9755-58a4984bb89a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_maximal_completion__p2m_f10915d7_3b63_441c_afee_bba7154a1b1e_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_f10915d7_3b63_441c_afee_bba7154a1b1e_a1
import Theorems.Thm_WilliamsonShmoys_edge_ncard_mono__p2m_f10915d7_3b63_441c_afee_bba7154a1b1e_a1
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hConn : L.Connected)
    (hV : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hEdges, hDrawH, hMax⟩ :=
    WilliamsonShmoys.planar_maximal_completion__p2m_f10915d7_3b63_441c_afee_bba7154a1b1e_a1
      L hDraw hV
  have hExact :=
    WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_f10915d7_3b63_441c_afee_bba7154a1b1e_a1
      H hDrawH hMax hV
  have hMono :=
    WilliamsonShmoys.edge_ncard_mono__p2m_f10915d7_3b63_441c_afee_bba7154a1b1e_a1
      L H hEdges
  omega
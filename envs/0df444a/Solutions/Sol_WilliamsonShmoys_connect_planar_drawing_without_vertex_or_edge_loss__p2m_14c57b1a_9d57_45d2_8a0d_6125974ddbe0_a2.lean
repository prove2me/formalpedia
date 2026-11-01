-- Prove2me | solution 1 for WilliamsonShmoys.connect_planar_drawing_without_vertex_or_edge_loss__p2m_14c57b1a_9d57_45d2_8a0d_6125974ddbe0_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:49:05.213461+00:00
-- url     : https://prove2.me/submissions/d7e11d46-2f33-4559-be45-b5bf4e072af5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_inclusion_maximal_drawable_supergraph__p2m_a79da144_fcf1_49a7_8693_9dcdff9b3064_a2
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_connected__p2m_a79da144_fcf1_49a7_8693_9dcdff9b3064_a2
import Theorems.Thm_WilliamsonShmoys_edge_ncard_mono__p2m_a79da144_fcf1_49a7_8693_9dcdff9b3064_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      L ≤ H ∧ HasPlanarDrawingOn H ∧ H.Connected ∧
        L.edgeSet.ncard ≤ H.edgeSet.ncard := by
  obtain ⟨M, hLM, hM, hmax⟩ :=
    WilliamsonShmoys.exists_inclusion_maximal_drawable_supergraph__p2m_a79da144_fcf1_49a7_8693_9dcdff9b3064_a2
      L hL
  exact ⟨M, hLM, hM,
    WilliamsonShmoys.maximal_drawable_graph_connected__p2m_a79da144_fcf1_49a7_8693_9dcdff9b3064_a2
      M hcard hM hmax,
    WilliamsonShmoys.edge_ncard_mono__p2m_a79da144_fcf1_49a7_8693_9dcdff9b3064_a2 hLM⟩
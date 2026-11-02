-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_triangulation_extension__p2m_8f2b622d_d69e_48f3_b5b2_9dea858b8d8f_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:38:22.575657+00:00
-- url     : https://prove2.me/submissions/975480f7-6a76-4530-932a-9570a5d71a03
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension__p2m_584708af_d974_4efc_b22f_05859fd9ba8d_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_has_triangulation_edge_count__p2m_584708af_d974_4efc_b22f_05859fd9ba8d_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 <= Fintype.card V) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
        H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨H, hGH, hPlanar, hCardinal, hMaximal⟩ :=
    WilliamsonShmoys.exists_maximal_planar_extension__p2m_584708af_d974_4efc_b22f_05859fd9ba8d_a1
      G hG
  have hEdges :=
    WilliamsonShmoys.maximal_planar_graph_has_triangulation_edge_count__p2m_584708af_d974_4efc_b22f_05859fd9ba8d_a1
      H hPlanar hMaximal hCard
  exact ⟨H, hGH, hPlanar, hCardinal, hEdges⟩
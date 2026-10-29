-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_bc657f31_eaae_4f57_ab42_14b02319f13d_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T21:44:45.014195+00:00
-- url     : https://prove2.me/submissions/db8e4ab8-04c6-464b-a7ea-4613ee54d8b9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_extension__p2m_96ae6d88_fda1_42e5_9f5b_cc899dd909d2_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_96ae6d88_fda1_42e5_9f5b_cc899dd909d2_a2
import Theorems.Thm_WilliamsonShmoys_subgraph_edgeSet_ncard_le__p2m_96ae6d88_fda1_42e5_9f5b_cc899dd909d2_a2

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hGH, hHPlanar, hHMaximal⟩ :=
    WilliamsonShmoys.planar_drawing_has_maximal_extension__p2m_96ae6d88_fda1_42e5_9f5b_cc899dd909d2_a2
      G hG
  have hHCount :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_96ae6d88_fda1_42e5_9f5b_cc899dd909d2_a2
      H hHPlanar hHMaximal hCard
  have hSubCount :=
    WilliamsonShmoys.subgraph_edgeSet_ncard_le__p2m_96ae6d88_fda1_42e5_9f5b_cc899dd909d2_a2
      G H hGH
  omega
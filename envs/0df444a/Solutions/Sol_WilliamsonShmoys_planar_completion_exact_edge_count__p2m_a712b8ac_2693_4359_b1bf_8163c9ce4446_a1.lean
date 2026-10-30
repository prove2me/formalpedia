-- Prove2me | solution 1 for WilliamsonShmoys.planar_completion_exact_edge_count__p2m_a712b8ac_2693_4359_b1bf_8163c9ce4446_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:29:06.846098+00:00
-- url     : https://prove2.me/submissions/4bdae8ed-a238-48f4-a928-ceb84a13e663

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_completion_maximal_drawable_supergraph__p2m_d5ea2124_1838_4ceb_a0a8_373ec58ed0bb_a1
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count__p2m_d5ea2124_1838_4ceb_a0a8_373ec58ed0bb_a1

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hDraw : HasPlanarDrawingOn H)
    (hCard : 3 <= Fintype.card V) :
    Exists fun K : SimpleGraph V =>
      And (Set.Subset H.edgeSet K.edgeSet)
        (And (HasPlanarDrawingOn K)
          (K.edgeSet.ncard + 6 = 3 * Fintype.card V)) := by
  obtain ⟨K, hHK, hKdraw, hKmax⟩ :=
    WilliamsonShmoys.planar_completion_maximal_drawable_supergraph__p2m_d5ea2124_1838_4ceb_a0a8_373ec58ed0bb_a1
      H hDraw
  have hcount :=
    WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_d5ea2124_1838_4ceb_a0a8_373ec58ed0bb_a1
      K hKdraw hCard hKmax
  exact ⟨K, hHK, hKdraw, hcount⟩

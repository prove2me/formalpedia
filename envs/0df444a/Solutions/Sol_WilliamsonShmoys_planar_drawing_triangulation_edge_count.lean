-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T04:25:48.599094+00:00
-- url     : https://prove2.me/submissions/88ac76c3-6185-4178-a113-409ba616b4de

import Theorems.Thm_WilliamsonShmoys_planar_drawing_exists_maximal_supergraph
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_from_arc_geometry

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
        M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨M, hLM, hM, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_exists_maximal_supergraph L hL
  exact ⟨M, hLM, hM,
    WilliamsonShmoys.maximal_planar_drawing_edge_count_from_arc_geometry
      M hV hM hmax⟩
-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_with_triangulation_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T09:38:15.488112+00:00
-- url     : https://prove2.me/submissions/72360348-a107-4e98-b9e5-7408166fe409

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_with_drawing_arcs
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_via_faces

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hKL, hL, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_with_drawing_arcs K hK
  have hcount :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count_via_faces L hV hL hmax
  exact ⟨L, hKL, hL, hcount⟩
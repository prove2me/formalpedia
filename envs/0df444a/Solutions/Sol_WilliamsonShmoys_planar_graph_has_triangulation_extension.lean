-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_has_triangulation_extension
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T23:20:45.231955+00:00
-- url     : https://prove2.me/submissions/c737587f-fbaf-46e4-ab49-5a25bb05c733

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_extension
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨L, hKL, hLplanar, hLmax⟩ :=
    WilliamsonShmoys.exists_edge_maximal_planar_extension K hK
  exact ⟨L, hKL, hLplanar,
    WilliamsonShmoys.maximal_planar_edge_count L hLplanar hV hLmax⟩
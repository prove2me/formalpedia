-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_exists
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T22:20:50.308462+00:00
-- url     : https://prove2.me/submissions/c98938a8-caa2-4fd9-8325-aa03520ceed9

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_exists_edge_maximal_extension
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_exists_maximal_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hKplanar : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hKL, hLplanar, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_exists_edge_maximal_extension K hKplanar
  exact ⟨L, hKL, hLplanar,
    WilliamsonShmoys.planar_drawing_triangulation_exists_maximal_edge_count L hV hLplanar hmax⟩
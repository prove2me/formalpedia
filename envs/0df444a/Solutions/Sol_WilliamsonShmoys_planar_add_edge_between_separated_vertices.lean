-- Prove2me | solution 1 for WilliamsonShmoys.planar_add_edge_between_separated_vertices
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T15:32:20.341997+00:00
-- url     : https://prove2.me/submissions/06546651-ae12-484c-a19e-2373845c3617
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_add_edge_between_separated_vertices_geometry
import Theorems.Thm_WilliamsonShmoys_edge_count_strict_of_new_edge

set_option autoImplicit false

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (u v : V)
    (hSeparated : ¬ H.Reachable u v)
    (hHdraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        H.edgeSet.ncard < K.edgeSet.ncard := by
  obtain ⟨K, hHK, hNew, hKdraw⟩ :=
    WilliamsonShmoys.planar_add_edge_between_separated_vertices_geometry
      H u v hSeparated hHdraw
  exact ⟨K, hHK, hKdraw,
    WilliamsonShmoys.edge_count_strict_of_new_edge H K u v hHK hSeparated hNew⟩
-- Prove2me | solution 1 for WilliamsonShmoys.planar_augmentation_edge_count_fixed_vertices
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T17:11:16.170036+00:00
-- url     : https://prove2.me/submissions/ff17c8e1-25c1-4537-8534-a5d7dadfa178
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_fixed_vertices
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_fixed_vertices

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hKL, hLDraw, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_fixed_vertices K hDraw
  have hEdgeCount : L.edgeSet.ncard + 6 = 3 * Fintype.card V :=
    WilliamsonShmoys.maximal_planar_edge_count_fixed_vertices L hV hLDraw hmax
  exact ⟨L, hKL, hLDraw, hEdgeCount⟩
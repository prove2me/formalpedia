-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_triangulation_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T08:15:28.158906+00:00
-- url     : https://prove2.me/submissions/c6333e24-2deb-493f-a513-f00b1f7d2b8c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal_extension
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_from_drawing

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ H : SimpleGraph V,
      L ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨H, hLH, hH, hmax⟩ :=
    WilliamsonShmoys.planar_supergraph_maximal_extension L hV hL
  exact ⟨H, hLH, hH,
    WilliamsonShmoys.maximal_planar_edge_count_from_drawing H hV hH hmax⟩
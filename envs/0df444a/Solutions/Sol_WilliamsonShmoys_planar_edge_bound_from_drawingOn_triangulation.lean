-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_bound_from_drawingOn_triangulation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T10:32:26.087228+00:00
-- url     : https://prove2.me/submissions/d6baa171-63b6-4012-bf35-a19029dd123b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_maximal_extension_df5b7716_886f_4c81_a3fd_ebfa1ccd5c5b
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_edge_count_df5b7716_886f_4c81_a3fd_ebfa1ccd5c5b

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, G ≤ H ∧ G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨H, hGH, hH, hmax⟩ :=
    WilliamsonShmoys.planar_drawingOn_maximal_extension_df5b7716_886f_4c81_a3fd_ebfa1ccd5c5b G hG
  have hcard :=
    WilliamsonShmoys.maximal_planar_drawingOn_edge_count_df5b7716_886f_4c81_a3fd_ebfa1ccd5c5b H hH hV hmax
  exact ⟨H, hGH, Set.ncard_mono (SimpleGraph.edgeSet_mono hGH), hH, hcard⟩
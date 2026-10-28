-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_planar_upper_retry3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T15:07:44.57066+00:00
-- url     : https://prove2.me/submissions/a779d894-8a7f-43ac-a5a8-03f60cd7ded4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_edge_count_planar_upper_retry3_exists_maximal_supergraph
import Theorems.Thm_WilliamsonShmoys_edge_count_planar_upper_retry3_maximal_edge_bound

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hDraw : HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨H, hGH, hHDraw, hHmax, hEdges⟩ :=
    WilliamsonShmoys.edge_count_planar_upper_retry3_exists_maximal_supergraph
      G hDraw
  have hBound :=
    WilliamsonShmoys.edge_count_planar_upper_retry3_maximal_edge_bound
      H hHDraw hCard hHmax
  exact le_trans hEdges hBound
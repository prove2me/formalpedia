-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_graph_edge_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T04:56:35.7798+00:00
-- url     : https://prove2.me/submissions/45d35922-9141-4963-8328-3179b47f28ce
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawing_connectedExtension
import Theorems.Thm_WilliamsonShmoys_connectedPlanar_edgeBound

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hHdraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨K, hsub, hconn, hKdraw⟩ :=
    WilliamsonShmoys.planarDrawing_connectedExtension H hHdraw
  have hK := WilliamsonShmoys.connectedPlanar_edgeBound K hV hconn hKdraw
  exact (Set.ncard_le_ncard hsub).trans hK
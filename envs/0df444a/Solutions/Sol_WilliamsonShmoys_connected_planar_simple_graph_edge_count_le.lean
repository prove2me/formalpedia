-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_simple_graph_edge_count_le
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T04:29:56.168692+00:00
-- url     : https://prove2.me/submissions/33f14af0-d4aa-447f-805a-f64d065e07e3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hconn : P.Connected)
    (hV : 3 <= Fintype.card V) :
    P.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  obtain ⟨Q, hQdraw, hsub, hQcard⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation P hdraw hconn hV
  calc
    P.edgeSet.ncard ≤ Q.edgeSet.ncard := Set.ncard_mono hsub
    _ = 3 * Fintype.card V - 6 := hQcard
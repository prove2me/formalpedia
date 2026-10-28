-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_graph_edge_count_le
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T04:18:34.703109+00:00
-- url     : https://prove2.me/submissions/e7ffe38b-9c74-4c66-ac33-c8583ed00468
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_connected_extension
import Theorems.Thm_WilliamsonShmoys_connected_planar_simple_graph_edge_count_le

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hV : 3 <= Fintype.card V) :
    P.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  obtain ⟨Q, hsub, hdrawQ, hconnQ, hmono⟩ :=
    WilliamsonShmoys.planar_drawingOn_connected_extension P hdraw hV
  exact hmono.trans
    (WilliamsonShmoys.connected_planar_simple_graph_edge_count_le Q hdrawQ hconnQ hV)
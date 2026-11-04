-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_bound_of_card_ge_three__p2m_511609d8_7f6a_4ba7_bd36_d7671338159d_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-03T21:17:08.642576+00:00
-- url     : https://prove2.me/submissions/59a17853-a3c2-4fcc-9977-87e6f59c022d

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_edge_bound
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hcard : 3 ≤ Fintype.card V) :
    L.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by
  rw [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset]
  exact WilliamsonShmoys.planar_drawingOn_edge_bound L hL hcard

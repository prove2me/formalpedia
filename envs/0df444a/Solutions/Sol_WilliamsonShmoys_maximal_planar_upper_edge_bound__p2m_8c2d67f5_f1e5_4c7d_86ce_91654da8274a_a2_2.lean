-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_upper_edge_bound__p2m_8c2d67f5_f1e5_4c7d_86ce_91654da8274a_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T11:55:05.470463+00:00
-- url     : https://prove2.me/submissions/6fc75781-3591-4a78-aa13-4be40185a9c9

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_edge_bound
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hn : 3 <= Fintype.card V) :
    L.edgeFinset.card <= 3 * Fintype.card V - 6 := by
  classical
  have h := WilliamsonShmoys.planar_drawingOn_edge_bound L hL hn
  rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset] at h
  exact h

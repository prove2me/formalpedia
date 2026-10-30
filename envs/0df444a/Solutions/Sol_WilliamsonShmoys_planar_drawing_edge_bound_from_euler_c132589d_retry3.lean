-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_bound_from_euler_c132589d_retry3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T00:12:11.776363+00:00
-- url     : https://prove2.me/submissions/99d3536b-d245-4b74-b641-184485cb0ed6

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph_exists_retry3
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_edge_bound_retry3

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hDraw : HasPlanarDrawingOn L) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hLH, hDrawH, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_supergraph_exists_retry3 L hDraw
  have hBound :=
    WilliamsonShmoys.planar_drawing_maximal_edge_bound_retry3 H hCard hDrawH hMax
  have hEdges : L.edgeSet ⊆ H.edgeSet := SimpleGraph.edgeSet_mono hLH
  have hCount : L.edgeSet.ncard ≤ H.edgeSet.ncard := Set.ncard_le_ncard hEdges
  omega
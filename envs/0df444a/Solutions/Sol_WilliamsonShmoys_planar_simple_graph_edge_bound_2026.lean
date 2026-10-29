-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_graph_edge_bound_2026
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T00:34:42.659765+00:00
-- url     : https://prove2.me/submissions/1f5d3c7a-ef7d-408c-a562-c4288b844fc7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_eulerData_2026__p2m_43f98bfb_7424_41c7_97de_56fe6ca417c5_a4

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨edgeCount, faceCount, hOriginal, hEuler, hIncidence⟩ :=
    WilliamsonShmoys.planarDrawingOn_eulerData_2026__p2m_43f98bfb_7424_41c7_97de_56fe6ca417c5_a4
      L hL hCard
  omega
-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound_35554814_repair3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T08:39:25.664613+00:00
-- url     : https://prove2.me/submissions/f3cded89-a348-41c1-ba9c-bb21916764b2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_connectivity_completion
import Theorems.Thm_WilliamsonShmoys_connected_drawing_edge_count_bound

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P) :
    P.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨Q, hQPlanar, hQConnected, hEdgeCount⟩ :=
    WilliamsonShmoys.planar_connectivity_completion P hCard hP
  have hQBound :=
    WilliamsonShmoys.connected_drawing_edge_count_bound Q hCard hQConnected hQPlanar
  omega
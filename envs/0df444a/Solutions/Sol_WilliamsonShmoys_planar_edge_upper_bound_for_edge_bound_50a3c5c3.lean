-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_upper_bound_for_edge_bound_50a3c5c3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T14:03:14.199867+00:00
-- url     : https://prove2.me/submissions/b31f1e86-6070-4368-92a2-e6f897e35451
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_supergraph_for_edge_bound
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_count_bound

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hQdraw : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hCard : 3 ≤ Fintype.card V) :
    Q.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hHconn, hHdraw, hEdges⟩ :=
    WilliamsonShmoys.planar_drawing_connected_supergraph_for_edge_bound Q hQdraw hCard
  have hBound :=
    WilliamsonShmoys.connected_planar_drawing_edge_count_bound H hHdraw hHconn hCard
  omega
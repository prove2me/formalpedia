-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_bound_from_drawing_9064c577
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T15:12:45.712217+00:00
-- url     : https://prove2.me/submissions/b18243d1-f3b7-475c-a6ca-3f5997760862

import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_from_triangulated_extension_9064c577
import Theorems.Thm_WilliamsonShmoys_edge_bound_of_subgraph_count_9064c577

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hSub, _hDrawH, hCount⟩ :=
    WilliamsonShmoys.planar_drawing_edge_bound_from_triangulated_extension_9064c577
      K hDraw hCard
  exact WilliamsonShmoys.edge_bound_of_subgraph_count_9064c577 K H hSub hCount
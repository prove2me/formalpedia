-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_count_for_face_equations_e86e41b9
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T12:47:01.855779+00:00
-- url     : https://prove2.me/submissions/e1b34ed6-0c0d-438d-81eb-c93d10eebbf8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_graph_completion_edge_count

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hMax : forall M : SimpleGraph V, L <= M -> HasPlanarDrawingOn M -> M = L)
    (hCard : 3 <= Fintype.card V) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨H, hLH, hH, hCount⟩ :=
    WilliamsonShmoys.drawable_graph_completion_edge_count L hL hCard
  have hHL : H = L := hMax H hLH hH
  simpa [hHL] using hCount
-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound_from_drawing_6e15fe35
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T02:51:35.391491+00:00
-- url     : https://prove2.me/submissions/df067871-1276-4bd5-8f53-9d49459494c2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_augment_edge_bound

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (hMax : forall N : SimpleGraph V, M <= N -> HasPlanarDrawingOn N -> M = N)
    (hCard : 3 <= Fintype.card V) :
    3 * Fintype.card V <= M.edgeSet.ncard + 6 := by
  obtain ⟨N, hMN, hN, hBound⟩ :=
    WilliamsonShmoys.planar_graph_augment_edge_bound M hM hCard
  have hEq : M = N := hMax N hMN hN
  simpa [hEq] using hBound
-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawing_edge_count_lower__p2m_9c5c2913_8662_47f3_b676_c48b7de0b279_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:56:10.259623+00:00
-- url     : https://prove2.me/submissions/3b5c2b29-2d81-4921-bb6a-5d66105e65ac
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_count_lower__p2m_ce0752f6_2cc0_436b_9908_f6f14786777a_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : forall N : SimpleGraph V, M <= N ->
      WilliamsonShmoys.HasPlanarDrawingOn N -> N = M)
    (hCard : 3 <= Fintype.card V) :
    3 * Fintype.card V <= M.edgeSet.ncard + 6 := by
  obtain ⟨N, hMN, hNDraw, hBound⟩ :=
    WilliamsonShmoys.planar_supergraph_edge_count_lower__p2m_ce0752f6_2cc0_436b_9908_f6f14786777a_a1
      M hDraw hCard
  have hEq : N = M := hMax N hMN hNDraw
  simpa [hEq] using hBound
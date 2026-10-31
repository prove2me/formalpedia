-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_count__p2m_db367b77_db98_427b_b1c6_513aa1e72eeb_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:23:06.973689+00:00
-- url     : https://prove2.me/submissions/dc54b1a5-b86e-46d0-9bb4-50cfef5a0710

import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_e8ae6a5a_5a4c_4f53_9707_6853e31c2747_a4

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V) (hDraw : HasPlanarDrawingOn P)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ Q : SimpleGraph V, P ≤ Q → HasPlanarDrawingOn Q → Q ≤ P) :
    P.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_e8ae6a5a_5a4c_4f53_9707_6853e31c2747_a4 P hDraw hV hMax

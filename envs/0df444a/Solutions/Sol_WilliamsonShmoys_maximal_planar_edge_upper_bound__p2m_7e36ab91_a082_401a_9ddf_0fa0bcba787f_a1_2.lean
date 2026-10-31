-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_upper_bound__p2m_7e36ab91_a082_401a_9ddf_0fa0bcba787f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:21:26.290406+00:00
-- url     : https://prove2.me/submissions/5b2ae721-0bd7-4784-9e76-53489c2f9e1e

import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound_repair3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hG : HasPlanarDrawingOn G) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.planar_drawing_edge_upper_bound_repair3 G hV hG

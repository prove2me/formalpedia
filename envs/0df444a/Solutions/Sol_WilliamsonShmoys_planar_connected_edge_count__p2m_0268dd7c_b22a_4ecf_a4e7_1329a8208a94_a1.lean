-- Prove2me | solution 1 for WilliamsonShmoys.planar_connected_edge_count__p2m_0268dd7c_b22a_4ecf_a4e7_1329a8208a94_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T21:31:40.587703+00:00
-- url     : https://prove2.me/submissions/fbec2168-76fb-4604-863e-55b307704ddf

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound__p2m_7f8156d0_59cd_483d_b914_1d18d842c166_a2

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hV : 3 <= Fintype.card V) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  exact WilliamsonShmoys.planar_edge_bound__p2m_7f8156d0_59cd_483d_b914_1d18d842c166_a2 G hG hV
-- Prove2me | solution 1 for WilliamsonShmoys.planar_connected_edge_count_bound__p2m_2911e589_9855_41f2_81aa_874f2d2a0dd0_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:52:15.965145+00:00
-- url     : https://prove2.me/submissions/289fd94e-7716-43a4-be05-30abdc719882
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_maximal_extension__p2m_3662a54d_ea7a_4ea3_804a_c2f8a32e2408_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_3662a54d_ea7a_4ea3_804a_c2f8a32e2408_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hV : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hGH, hHplanar, hHconn, hHmax, hcard⟩ :=
    WilliamsonShmoys.planar_maximal_extension__p2m_3662a54d_ea7a_4ea3_804a_c2f8a32e2408_a1
      G hG hconn hV
  have hEq :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_3662a54d_ea7a_4ea3_804a_c2f8a32e2408_a1
      H hHplanar hHconn hV hHmax
  omega
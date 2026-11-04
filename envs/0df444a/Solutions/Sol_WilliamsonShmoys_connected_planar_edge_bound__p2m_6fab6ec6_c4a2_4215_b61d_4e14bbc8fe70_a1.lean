-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_bound__p2m_6fab6ec6_c4a2_4215_b61d_4e14bbc8fe70_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-03T16:39:50.059389+00:00
-- url     : https://prove2.me/submissions/49de8dd9-7534-4330-b31f-205e8f0102b2

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_euler_bound__p2m_fa5d736f_5e40_4868_bcf6_007f98212d2a_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G) (hconn : G.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    letI : DecidableRel G.Adj := dG
    G.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by
  have hd : dG = Classical.decRel G.Adj := Subsingleton.elim _ _
  subst dG
  exact Nat.le_sub_of_add_le
    (WilliamsonShmoys.connected_planar_euler_bound__p2m_fa5d736f_5e40_4868_bcf6_007f98212d2a_a1 G hG hconn hcard)

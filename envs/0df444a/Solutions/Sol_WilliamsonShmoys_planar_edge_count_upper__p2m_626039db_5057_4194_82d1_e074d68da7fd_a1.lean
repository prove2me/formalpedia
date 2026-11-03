-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper__p2m_626039db_5057_4194_82d1_e074d68da7fd_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:18:54.82183+00:00
-- url     : https://prove2.me/submissions/8ab9610a-1dc1-4bc8-936b-cb55a171d50c

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_connected_upper__p2m_8a1edb89_91b7_4c19_a333_1779b45ebb8a_a1
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_from_connected__p2m_8a1edb89_91b7_4c19_a333_1779b45ebb8a_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel G.Adj := dG
     G.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by
  exact WilliamsonShmoys.planar_edge_count_from_connected__p2m_8a1edb89_91b7_4c19_a333_1779b45ebb8a_a1
    G dG
    (fun H dH hconn hplanar hcard =>
      WilliamsonShmoys.planar_edge_count_connected_upper__p2m_8a1edb89_91b7_4c19_a333_1779b45ebb8a_a1
        H dH hconn hplanar hcard)
    hG hcard
-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_3662a54d_ea7a_4ea3_804a_c2f8a32e2408_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T01:02:52.217636+00:00
-- url     : https://prove2.me/submissions/7d393096-f59d-4caf-a46c-72d5e135d37a

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper__p2m_1563787d_1e9d_4e0d_aca3_7df10f22af54_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower__p2m_1563787d_1e9d_4e0d_aca3_7df10f22af54_a1

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hV : 3 <= Fintype.card V)
    (hmax : forall K : SimpleGraph V,
      H <= K -> WilliamsonShmoys.HasPlanarDrawingOn K -> K <= H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hupper := WilliamsonShmoys.planar_edge_count_upper__p2m_1563787d_1e9d_4e0d_aca3_7df10f22af54_a1
    H hH hconn hV
  have hlower := WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_1563787d_1e9d_4e0d_aca3_7df10f22af54_a1
    H hH hconn hV hmax
  omega
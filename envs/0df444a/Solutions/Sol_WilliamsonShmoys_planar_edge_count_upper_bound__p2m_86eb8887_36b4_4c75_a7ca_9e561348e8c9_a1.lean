-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_86eb8887_36b4_4c75_a7ca_9e561348e8c9_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:03:49.970194+00:00
-- url     : https://prove2.me/submissions/b125e161-7cad-4940-b91e-abdb40baed33

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_connected__p2m_bd57f3c8_e371_4c77_9b1f_383221a33d80_a3
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_disconnected__p2m_bd57f3c8_e371_4c77_9b1f_383221a33d80_a3

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hcard : 3 <= Fintype.card V)
    (hK : HasPlanarDrawingOn K) :
    letI : (L : SimpleGraph V) -> DecidableRel L.Adj :=
      fun L => Classical.decRel L.Adj
    K.edgeFinset.card <= 3 * Fintype.card V - 6 := by
  classical
  by_cases hconn : K.Connected
  · exact WilliamsonShmoys.planar_edge_count_connected__p2m_bd57f3c8_e371_4c77_9b1f_383221a33d80_a3
      K hcard hconn hK
  · exact WilliamsonShmoys.planar_edge_count_disconnected__p2m_bd57f3c8_e371_4c77_9b1f_383221a33d80_a3
      K hcard hconn hK
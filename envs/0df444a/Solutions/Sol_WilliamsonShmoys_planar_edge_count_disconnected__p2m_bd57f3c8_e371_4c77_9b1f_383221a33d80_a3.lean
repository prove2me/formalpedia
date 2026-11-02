-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_disconnected__p2m_bd57f3c8_e371_4c77_9b1f_383221a33d80_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:06:14.75847+00:00
-- url     : https://prove2.me/submissions/535ea76f-57dc-441d-ac88-0bc9a1f85e64
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_component_edge_bound__p2m_6875723b_f815_435e_a204_8de0d4b60ca9_a3
import Theorems.Thm_WilliamsonShmoys_disconnected_component_aggregation__p2m_6875723b_f815_435e_a204_8de0d4b60ca9_a3
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hcard : 3 <= Fintype.card V)
    (hdisconn : ¬ K.Connected)
    (hK : HasPlanarDrawingOn K) :
    letI : (L : SimpleGraph V) -> DecidableRel L.Adj :=
      fun L => Classical.decRel L.Adj
    K.edgeFinset.card <= 3 * Fintype.card V - 6 := by
  letI : (L : SimpleGraph V) -> DecidableRel L.Adj :=
    fun L => Classical.decRel L.Adj
  apply WilliamsonShmoys.disconnected_component_aggregation__p2m_6875723b_f815_435e_a204_8de0d4b60ca9_a3 K hcard hdisconn
  intro c
  exact WilliamsonShmoys.planar_component_edge_bound__p2m_6875723b_f815_435e_a204_8de0d4b60ca9_a3 K hK c
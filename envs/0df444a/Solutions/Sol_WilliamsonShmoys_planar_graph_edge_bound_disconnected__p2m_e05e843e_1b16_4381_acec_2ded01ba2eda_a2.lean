-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_edge_bound_disconnected__p2m_e05e843e_1b16_4381_acec_2ded01ba2eda_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:47:17.151187+00:00
-- url     : https://prove2.me/submissions/da6518dd-63b3-4800-bd72-79c9ac5b3d2c

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_graph_edge_bound_all__p2m_412cf563_cd90_4618_ba6d_11be264b4659_a3

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hconn : ¬ H.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj
     H.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by
  exact WilliamsonShmoys.planar_graph_edge_bound_all__p2m_412cf563_cd90_4618_ba6d_11be264b4659_a3
    H hcard hdraw
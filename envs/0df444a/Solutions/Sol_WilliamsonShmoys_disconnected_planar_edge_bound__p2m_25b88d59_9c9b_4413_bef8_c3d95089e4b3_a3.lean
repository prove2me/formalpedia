-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_planar_edge_bound__p2m_25b88d59_9c9b_4413_bef8_c3d95089e4b3_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:18:33.054743+00:00
-- url     : https://prove2.me/submissions/15364744-a001-4485-b16f-2a108aeb2f72
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_disconnected_planar_connected_extension__p2m_286af89a_075e_437e_a01f_e70735543bba_a1
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_286af89a_075e_437e_a01f_e70735543bba_a1

set_option autoImplicit false

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hdisconn : ¬ N.Connected) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj
     N.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by
  classical
  letI : DecidableRel N.Adj := Classical.decRel N.Adj
  obtain ⟨H, hle, hcard_le, hconn, hH⟩ :=
    WilliamsonShmoys.disconnected_planar_connected_extension__p2m_286af89a_075e_437e_a01f_e70735543bba_a1
      N hcard hN hdisconn
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  exact Nat.le_trans hcard_le
    (WilliamsonShmoys.connected_planar_edge_bound__p2m_286af89a_075e_437e_a01f_e70735543bba_a1
      H hcard hconn hH)
-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_count_bound__p2m_2cf5c394_8fe3_4b96_8033_bf5d04367b46_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:18:40.421121+00:00
-- url     : https://prove2.me/submissions/76577685-10a4-4934-a2c3-6d3adebd6477
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_face_count_certificate__p2m_230ef2ff_d0ad_4b7a_9595_07bea2af44fc_a1
import Theorems.Thm_WilliamsonShmoys_euler_face_count_edge_bound__p2m_230ef2ff_d0ad_4b7a_9595_07bea2af44fc_a1

open WilliamsonShmoys
open scoped BigOperators
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L) (hconn : L.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel L.Adj := Classical.decRel L.Adj;
      L.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by
  classical
  letI : DecidableRel L.Adj := Classical.decRel L.Adj
  obtain ⟨F, ell, hEuler, hsum, hlen⟩ :=
    WilliamsonShmoys.connected_planar_drawing_face_count_certificate__p2m_230ef2ff_d0ad_4b7a_9595_07bea2af44fc_a1
      L hL hconn hcard
  exact WilliamsonShmoys.euler_face_count_edge_bound__p2m_230ef2ff_d0ad_4b7a_9595_07bea2af44fc_a1
    ell hEuler hsum hlen
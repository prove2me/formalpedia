-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_upper_bound_connected_case__p2m_263e0430_0bed_4695_a55f_33a5be744a5b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:46:32.466987+00:00
-- url     : https://prove2.me/submissions/978f983e-9f8f-461a-a945-d7745c4c0491

import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_7bba71c9_ccd8_4c5e_9f36_6c106eba0d6c_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_7bba71c9_ccd8_4c5e_9f36_6c106eba0d6c_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hconn : N.Connected) (hN : HasPlanarDrawingOn N) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj;
     N.edgeFinset.card + 6 <= 3 * Fintype.card V) := by
  letI : DecidableRel N.Adj := Classical.decRel N.Adj
  obtain ⟨H, hNH, hH, hmax, hcard⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension__p2m_7bba71c9_ccd8_4c5e_9f36_6c106eba0d6c_a1
      N hconn hN
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  have hHcount :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_7bba71c9_ccd8_4c5e_9f36_6c106eba0d6c_a1
      H hV hH hmax
  omega
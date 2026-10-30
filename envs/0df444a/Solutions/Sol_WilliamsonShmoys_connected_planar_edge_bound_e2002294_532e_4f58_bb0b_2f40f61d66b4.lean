-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_bound_e2002294_532e_4f58_bb0b_2f40f61d66b4
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T18:14:25.634994+00:00
-- url     : https://prove2.me/submissions/fb2eccea-faae-46a5-ad4f-8fd69090270c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_face_data_1770f0d3_7ba6_4c26_9dfc_b5672704155a
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound_of_euler_data_1770f0d3_7ba6_4c26_9dfc_b5672704155a

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hconn : K.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V) :
    K.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  let hData :=
    WilliamsonShmoys.planar_drawing_euler_face_data_1770f0d3_7ba6_4c26_9dfc_b5672704155a
      K hconn hdraw hV
  exact WilliamsonShmoys.connected_planar_edge_bound_of_euler_data_1770f0d3_7ba6_4c26_9dfc_b5672704155a
    K (Classical.choose hData) (Classical.choose_spec hData).1
      (Classical.choose_spec hData).2
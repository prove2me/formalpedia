-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_bound__p2m_dccace07_71ac_4a60_a538_34fe866b4edd_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:42:18.106039+00:00
-- url     : https://prove2.me/submissions/5b67c8a4-b3f5-488d-a546-a1d8a7bf9665

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_face_count_bound__p2m_af58f30d_9690_4bf2_bfba_5c068b1bd46b_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hDraw : HasPlanarDrawingOn G)
    (hConnected : G.Connected) (hCard : 3 <= Fintype.card V) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  have hface :=
    WilliamsonShmoys.connected_planar_face_count_bound__p2m_af58f30d_9690_4bf2_bfba_5c068b1bd46b_a1
      G hDraw hConnected hCard
  cases hface with
  | intro f hf =>
    cases hf with
    | intro hEuler hFaceSides => omega
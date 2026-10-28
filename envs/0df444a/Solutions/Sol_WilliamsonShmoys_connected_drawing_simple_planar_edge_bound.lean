-- Prove2me | solution 1 for WilliamsonShmoys.connected_drawing_simple_planar_edge_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T10:08:01.924359+00:00
-- url     : https://prove2.me/submissions/cbe6c340-de61-4452-9d52-df8dc9eb02c0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_drawing_euler_face_count
import Theorems.Thm_WilliamsonShmoys_connected_drawing_face_incidence_bound

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hConn : G.Connected)
    (hCard : 3 <= Fintype.card V) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨f, hEuler⟩ :=
    WilliamsonShmoys.connected_drawing_euler_face_count G hG hConn
  have hIncidence :=
    WilliamsonShmoys.connected_drawing_face_incidence_bound
      G hG hConn hCard f hEuler
  omega
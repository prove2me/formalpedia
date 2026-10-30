-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_bound__p2m_09553c75_05d3_4866_a115_40c42a94c393_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T09:33:59.349559+00:00
-- url     : https://prove2.me/submissions/d11a13b3-9724-40a9-b28b-84e53a27ae48
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_face_walk_data__p2m_1aa142c3_2879_49d1_9ded_02a2d2269a9c_a2
import Theorems.Thm_WilliamsonShmoys_face_walk_counting_bound__p2m_1aa142c3_2879_49d1_9ded_02a2d2269a9c_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hConnected : H.Connected)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨faceLengths, hEuler, hSum, hFace⟩ :=
    WilliamsonShmoys.planar_drawing_has_face_walk_data__p2m_1aa142c3_2879_49d1_9ded_02a2d2269a9c_a2
      H hV hConnected hH
  exact WilliamsonShmoys.face_walk_counting_bound__p2m_1aa142c3_2879_49d1_9ded_02a2d2269a9c_a2
    H.edgeSet.ncard (Fintype.card V) faceLengths hEuler hSum hFace
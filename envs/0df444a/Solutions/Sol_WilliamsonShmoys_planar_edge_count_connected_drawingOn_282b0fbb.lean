-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_connected_drawingOn_282b0fbb
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T11:03:44.956034+00:00
-- url     : https://prove2.me/submissions/6864230e-0686-428a-8349-33e7e2e50018
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_face_walks_282b0fbb
import Theorems.Thm_WilliamsonShmoys_planar_face_count_arithmetic_282b0fbb

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 <= Fintype.card V)
    (hConnected : L.Connected) :
    (L.edgeSet.ncard : Int) <= 3 * (Fintype.card V : Int) - 6 := by
  obtain ⟨faces, hEuler, hIncidence, hFaceLength⟩ :=
    WilliamsonShmoys.planar_drawing_face_walks_282b0fbb
      L hL hCard hConnected
  exact WilliamsonShmoys.planar_face_count_arithmetic_282b0fbb
    (Fintype.card V) L.edgeSet.ncard faces hCard hEuler hIncidence hFaceLength
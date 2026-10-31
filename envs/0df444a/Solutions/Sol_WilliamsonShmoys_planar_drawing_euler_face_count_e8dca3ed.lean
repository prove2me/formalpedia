-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_face_count_e8dca3ed
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:45:28.385299+00:00
-- url     : https://prove2.me/submissions/b10e14de-db09-4839-b4af-dac1c9a569fe

import Theorems.Thm_WilliamsonShmoys_planar_drawing_face_count_data

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hConnected : G.Connected)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ f : ℕ,
      Fintype.card V + f = G.edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * G.edgeSet.ncard :=
  WilliamsonShmoys.planar_drawing_face_count_data G hV hConnected hDraw

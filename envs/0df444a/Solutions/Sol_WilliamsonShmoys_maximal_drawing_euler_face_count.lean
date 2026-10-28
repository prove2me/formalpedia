-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawing_euler_face_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T15:55:47.18257+00:00
-- url     : https://prove2.me/submissions/36c3f439-aa48-49c3-b766-1cdf0ede5fd0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_connected
import Theorems.Thm_WilliamsonShmoys_connected_drawing_euler_face_bound

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hmax : forall H : SimpleGraph V, G <= H ->
      WilliamsonShmoys.HasPlanarDrawingOn H -> H <= G)
    (hV : 3 <= Fintype.card V) :
    exists f : Nat,
      Fintype.card V + f = G.edgeSet.ncard + 2 /\
      3 * f <= 2 * G.edgeSet.ncard := by
  have hconn : G.Connected :=
    WilliamsonShmoys.maximal_drawable_connected G hdraw hmax hV
  exact WilliamsonShmoys.connected_drawing_euler_face_bound G hdraw hconn hV
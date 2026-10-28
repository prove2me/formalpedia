-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_face_count_data
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T05:12:40.973211+00:00
-- url     : https://prove2.me/submissions/bb1a2c60-04a0-4b31-bd49-9877afc458ef
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_face_count_from_embedding
import Theorems.Thm_WilliamsonShmoys_planar_drawing_simple_edge_bound_from_embedding

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hconn : G.Connected)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    Exists fun f : Nat => And
      (Fintype.card V + f = G.edgeSet.ncard + 2)
      (LE.le (3 * f) (2 * G.edgeSet.ncard)) := by
  have heuler :=
    WilliamsonShmoys.planar_drawing_euler_face_count_from_embedding G hconn hG
  have hedge :=
    WilliamsonShmoys.planar_drawing_simple_edge_bound_from_embedding G hV hconn hG
  cases heuler with
  | intro f hf =>
    apply Exists.intro f
    apply And.intro
    exact hf
    omega
-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_euler_face_certificate__p2m_792d8105_156d_4ec7_b9fb_1feb01e02200_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:47:24.903534+00:00
-- url     : https://prove2.me/submissions/c424a92e-9af0-4dc8-a368-3545e520a892
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_connected_planar_euler_face_count__p2m_5594ab01_5507_4608_93d6_8bce1469fe90_a2
import Theorems.Thm_WilliamsonShmoys_planar_euler_face_incidence_bound__p2m_5594ab01_5507_4608_93d6_8bce1469fe90_a2

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hconn : H.Connected)
    (hH : HasPlanarDrawingOn H)
    (hcard : 3 <= Fintype.card V) :
    letI : DecidableRel H.Adj := Classical.decRel H.Adj
    Exists fun f : Nat =>
      And (Fintype.card V + f = H.edgeFinset.card + 2)
          (3 * f <= 2 * H.edgeFinset.card) := by
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  cases WilliamsonShmoys.connected_planar_euler_face_count__p2m_5594ab01_5507_4608_93d6_8bce1469fe90_a2
      H hconn hH with
  | intro f hEuler =>
      exact Exists.intro f (And.intro hEuler
        (WilliamsonShmoys.planar_euler_face_incidence_bound__p2m_5594ab01_5507_4608_93d6_8bce1469fe90_a2
          H hconn hH hcard f hEuler))
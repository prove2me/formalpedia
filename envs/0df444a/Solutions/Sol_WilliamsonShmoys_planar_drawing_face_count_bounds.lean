-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_face_count_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T01:25:18.331495+00:00
-- url     : https://prove2.me/submissions/575c2fb5-2bea-450c-8e02-6c5e82390244

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_face_count_edge_bound
import Theorems.Thm_WilliamsonShmoys_connected_face_count_nonnegative
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hcard : 3 <= Fintype.card V) :
    Exists fun f : Nat =>
      And (Fintype.card V + f = G.edgeSet.ncard + 2)
          (3 * f <= 2 * G.edgeSet.ncard) := by
  have hedge := WilliamsonShmoys.planar_drawing_face_count_edge_bound G hG hcard
  have hconn' := WilliamsonShmoys.connected_face_count_nonnegative G hconn
  let f : Nat := G.edgeSet.ncard + 2 - Fintype.card V
  have heuler : Fintype.card V + f = G.edgeSet.ncard + 2 := by
    dsimp [f]
    omega
  have hface : 3 * f <= 2 * G.edgeSet.ncard := by
    dsimp [f]
    omega
  exact Exists.intro f (And.intro heuler hface)
-- Prove2me | solution 1 for WilliamsonShmoys.drawingOn_face_boundary_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T22:55:31.7311+00:00
-- url     : https://prove2.me/submissions/9291e983-fffa-48c9-a745-4cd74c11b9a1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawingOn_simple_planar_edge_bound
set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hconn : G.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) (f : Nat)
    (heuler : Fintype.card V + f = G.edgeSet.ncard + 2) :
    3 * f ≤ 2 * G.edgeSet.ncard := by
  have hedge := WilliamsonShmoys.drawingOn_simple_planar_edge_bound G hconn hdraw hcard
  omega
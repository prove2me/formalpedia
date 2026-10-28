-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_face_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T22:42:54.0084+00:00
-- url     : https://prove2.me/submissions/74ea4bb6-5178-4dd3-8506-abb62f888e4e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_components

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L)
    (hm : 2 ≤ L.edgeSet.ncard)
    (f c : ℕ)
    (heuler : Fintype.card V + f = L.edgeSet.ncard + c + 1) :
    3 * f ≤ 2 * L.edgeSet.ncard := by
  have hbound := WilliamsonShmoys.planar_drawing_edge_bound_components L hV hL hm c
  omega
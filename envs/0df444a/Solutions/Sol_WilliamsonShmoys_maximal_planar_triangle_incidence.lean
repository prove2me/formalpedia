-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_triangle_incidence
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T12:48:59.62067+00:00
-- url     : https://prove2.me/submissions/28a76f57-a274-4e0d-a5e8-9e02de083f55
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_d1156ce4

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn H)
    (hMax : forall J : SimpleGraph V, H <= J -> HasPlanarDrawingOn J -> J = H)
    (hCard : 3 <= Fintype.card V)
    (f : Nat) :
    Fintype.card V + f = H.edgeSet.ncard + 2 ->
    3 * f = 2 * H.edgeSet.ncard := by
  intro hEuler
  have hEdges := WilliamsonShmoys.maximal_planar_drawing_edge_count_d1156ce4 H hDraw hMax hCard
  omega
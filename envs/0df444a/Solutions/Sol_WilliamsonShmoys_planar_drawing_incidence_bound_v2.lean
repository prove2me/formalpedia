-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_incidence_bound_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T02:48:08.227018+00:00
-- url     : https://prove2.me/submissions/8eede34f-f2b8-40c3-b0de-0a3c236a2ac9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WilliamsonShmoys_simple_planar_edge_bound_any_components
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hLdraw : HasPlanarDrawingOn L)
    (hConnected : L.Connected)
    (hCard : 3 ≤ Fintype.card V)
    (f : ℕ)
    (hEuler : Fintype.card V + f = L.edgeSet.ncard + 2) :
    3 * f ≤ 2 * L.edgeSet.ncard := by
  have hEdge :=
    WilliamsonShmoys.simple_planar_edge_bound_any_components L hLdraw hCard
  omega
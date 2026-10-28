-- Prove2me | solution 1 for WilliamsonShmoys.simple_planar_edge_bound_disconnected
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T07:04:30.941992+00:00
-- url     : https://prove2.me/submissions/86e50678-32d2-4cad-8c0b-34d7a3164163
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion_same_vertex_set_bound68c1edf9

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hLdraw : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 <= Fintype.card V)
    (hDisconnected : Not L.Connected) :
    L.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨H, hDrawH, hSub, hEq⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_completion_same_vertex_set_bound68c1edf9
      L hLdraw hCard
  have hEdges : L.edgeSet.ncard <= H.edgeSet.ncard := Set.ncard_mono hSub
  omega
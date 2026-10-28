-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawable_graph_connected
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T14:41:21.171709+00:00
-- url     : https://prove2.me/submissions/e7dcdb62-70f4-4151-a597-9e2963d2910f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_add_edge_when_disconnected

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hHdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMaximal : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K →
      K.edgeSet.ncard ≤ H.edgeSet.ncard)
    (hCard : 3 ≤ Fintype.card V) :
    H.Connected := by
  by_contra hNotConnected
  obtain ⟨K, hHK, hKdraw, hEdges⟩ :=
    WilliamsonShmoys.planar_graph_add_edge_when_disconnected H hHdraw hCard hNotConnected
  have hMax := hMaximal K hHK hKdraw
  omega
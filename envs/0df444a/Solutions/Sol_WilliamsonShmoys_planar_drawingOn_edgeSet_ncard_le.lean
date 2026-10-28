-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawingOn_edgeSet_ncard_le
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T17:38:58.489999+00:00
-- url     : https://prove2.me/submissions/ae850fcb-8ad2-48a8-a57d-6d3af09a392c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_connected_extension
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_edgeSet_ncard_le_of_connected

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hCard : 3 <= Fintype.card V) :
    J.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  obtain ⟨K, hJK, hKConnected, hKDraw⟩ :=
    WilliamsonShmoys.planarDrawingOn_connected_extension J hDraw hCard
  have hBound := WilliamsonShmoys.planar_drawingOn_edgeSet_ncard_le_of_connected
    K hKDraw hCard hKConnected
  exact (Set.ncard_mono (SimpleGraph.edgeSet_mono hJK)).trans hBound
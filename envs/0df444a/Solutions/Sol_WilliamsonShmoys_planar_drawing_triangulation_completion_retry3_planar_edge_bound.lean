-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_completion_retry3_planar_edge_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T11:10:29.921499+00:00
-- url     : https://prove2.me/submissions/9da4370c-7fcc-466a-8d09-f20eb66ca0b4

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion_retry3_planar_edge_bound_triangulation_completion

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hDraw : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨T, hLT, hT⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_completion_retry3_planar_edge_bound_triangulation_completion
      L hDraw hCard
  have hEdges : L.edgeSet.ncard ≤ T.edgeSet.ncard :=
    Set.ncard_mono (SimpleGraph.edgeSet_mono hLT)
  rw [hT] at hEdges
  omega
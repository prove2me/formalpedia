-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_strict_supergraph_step
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T05:32:47.614331+00:00
-- url     : https://prove2.me/submissions/625372ee-d41f-445d-bb02-4aee1873d5ab
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_add_edge_across_components
import Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_lt_of_le_of_new_edge

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hDisconnected : ¬ G.Connected) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      G.edgeSet.ncard < H.edgeSet.ncard ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by
  obtain ⟨u, v, hnot, H, hGH, hadj, hH⟩ :=
    WilliamsonShmoys.planar_drawing_add_edge_across_components
      G hG hDisconnected
  refine ⟨H, hGH, ?_, hH⟩
  exact WilliamsonShmoys.edgeSet_ncard_lt_of_le_of_new_edge
    G H hGH u v hnot hadj
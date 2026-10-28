-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_upper_bound_c5c6f6ee
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T06:11:36.218948+00:00
-- url     : https://prove2.me/submissions/b8224792-7188-4e1c-9bbc-dbfedce96330
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_augmentation
import Theorems.Thm_WilliamsonShmoys_subgraph_edgeSet_ncard_le

set_option autoImplicit false

/-- Reduce the drawing to a triangulated supergraph, then compare edge counts. -/
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    M.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨H, hMH, hH, hcard⟩ :=
    WilliamsonShmoys.planar_drawing_augmentation M hV hM
  have hle : M.edgeSet.ncard <= H.edgeSet.ncard :=
    WilliamsonShmoys.subgraph_edgeSet_ncard_le M H hMH
  omega

-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_maximal_euler_count_upper_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T10:20:49.957995+00:00
-- url     : https://prove2.me/submissions/06eb8606-af3c-4d2a-85e5-2a04f5682684
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_from_drawingOn_triangulation
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, _hGH, hmono, _hH, htri⟩ :=
    WilliamsonShmoys.planar_edge_bound_from_drawingOn_triangulation G hG hV
  omega
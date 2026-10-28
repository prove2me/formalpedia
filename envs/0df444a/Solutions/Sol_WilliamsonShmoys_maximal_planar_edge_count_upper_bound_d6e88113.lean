-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_upper_bound_d6e88113
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T19:13:28.624672+00:00
-- url     : https://prove2.me/submissions/73e265b4-c980-46c0-882b-92ffbe431246
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_for_edge_bound_9f95e338
import Theorems.Thm_WilliamsonShmoys_edge_count_mono_9f95e338

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn H) (hV : 3 <= Fintype.card V) :
    H.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  rcases WilliamsonShmoys.planar_drawing_triangulation_for_edge_bound_9f95e338
      H hdraw hV with ⟨T, hsub, _hTdraw, hTcount⟩
  have hcount := WilliamsonShmoys.edge_count_mono_9f95e338 H T hsub
  omega
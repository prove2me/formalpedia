-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_bound_of_drawing__p2m_7c57b747_c460_4faf_9469_5a2ac820d0a0_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:44:20.501537+00:00
-- url     : https://prove2.me/submissions/c17ef18e-7786-4afd-8b64-4ddac3dbffcb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion__p2m_a893531d_2eaf_40a4_93f3_f4bc4ca725ea_a3

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hGH, hHdraw, hle, hHeq⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_completion__p2m_a893531d_2eaf_40a4_93f3_f4bc4ca725ea_a3
      G hG hV
  omega
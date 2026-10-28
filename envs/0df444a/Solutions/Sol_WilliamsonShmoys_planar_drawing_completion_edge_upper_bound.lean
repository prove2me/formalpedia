-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_completion_edge_upper_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T05:35:37.970405+00:00
-- url     : https://prove2.me/submissions/7bcc25bd-983b-43b7-bacb-94003176b6a7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_completion_extension_9c238260_8e64_40d3_b87d_42af728950e9
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_completion_edge_count_9c238260_8e64_40d3_b87d_42af728950e9

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hDrawing : HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hGH, hEdges, hHdraw, hMaximal⟩ :=
    WilliamsonShmoys.planar_drawing_completion_extension_9c238260_8e64_40d3_b87d_42af728950e9 G hDrawing
  have hCount :=
    WilliamsonShmoys.maximal_planar_drawing_completion_edge_count_9c238260_8e64_40d3_b87d_42af728950e9 H hHdraw hV hMaximal
  omega
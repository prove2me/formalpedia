-- Prove2me | solution 2 for WilliamsonShmoys.planar_simple_graph_edge_bound_for_maximal_drawing_20261026
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T18:15:09.330974+00:00
-- url     : https://prove2.me/submissions/aea6294a-65e7-44c2-99cc-3e97ef57d879
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_component_face_data
import Theorems.Thm_WilliamsonShmoys_planar_component_face_data_arithmetic

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  classical
  obtain ⟨parts, hNonempty, hDisjoint, hCover, hEdgeSum, hLocal⟩ :=
    WilliamsonShmoys.planar_drawing_component_face_data G hG
  exact WilliamsonShmoys.planar_component_face_data_arithmetic
    G parts hV hNonempty hDisjoint hCover hEdgeSum hLocal
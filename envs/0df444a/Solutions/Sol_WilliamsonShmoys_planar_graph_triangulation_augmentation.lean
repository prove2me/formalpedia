-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_triangulation_augmentation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T22:10:04.558972+00:00
-- url     : https://prove2.me/submissions/3e94e0f1-5b95-48c6-b89a-a7291c66bb6a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_finiteDrawing
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_finiteDrawing

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V) (hdraw : WilliamsonShmoys.HasPlanarDrawingOn U)
    (hV : 3 ≤ Fintype.card V) :
    ∃ W : SimpleGraph V, U ≤ W ∧ WilliamsonShmoys.HasPlanarDrawingOn W ∧
      3 * Fintype.card V = W.edgeSet.ncard + 6 := by
  obtain ⟨W, hUW, hdrawW, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_finiteDrawing U hdraw hV
  exact ⟨W, hUW, hdrawW,
    WilliamsonShmoys.maximal_planar_drawing_edge_count_finiteDrawing W hdrawW hV hmax⟩
-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawingOn_triangulation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T09:30:36.257287+00:00
-- url     : https://prove2.me/submissions/de94a247-d619-42ff-bf9c-4fe61f23984e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_supergraph_exists_6a6719d0_85b1_4f65_94e2_17fb35f78fa2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_edge_count_6a6719d0_85b1_4f65_94e2_17fb35f78fa2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    Exists fun M : SimpleGraph V =>
      G <= M /\
      WilliamsonShmoys.HasPlanarDrawingOn M /\
      3 * Fintype.card V = M.edgeSet.ncard + 6 := by
  obtain ⟨M, hGM, hM, hMax⟩ :=
    WilliamsonShmoys.maximal_planar_drawingOn_supergraph_exists_6a6719d0_85b1_4f65_94e2_17fb35f78fa2
      G hG
  exact ⟨M, hGM, hM,
    WilliamsonShmoys.maximal_planar_drawingOn_edge_count_6a6719d0_85b1_4f65_94e2_17fb35f78fa2
      M hV hM hMax⟩
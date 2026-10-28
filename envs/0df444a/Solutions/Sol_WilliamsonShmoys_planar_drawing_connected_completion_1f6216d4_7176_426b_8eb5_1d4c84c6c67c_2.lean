-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_connected_completion_1f6216d4_7176_426b_8eb5_1d4c84c6c67c
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T03:27:39.580304+00:00
-- url     : https://prove2.me/submissions/627c1570-fc2e-4ded-b6d4-6b66ee93b5f7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_add_edge_extension_1f6216d4_7176_426b_8eb5_1d4c84c6c67c
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_1f6216d4_7176_426b_8eb5_1d4c84c6c67c

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ K.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        H.edgeSet.ncard ≤ K.edgeSet.ncard := by
  obtain ⟨K, hsub, hconn, hdrawK⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension_1f6216d4_7176_426b_8eb5_1d4c84c6c67c
      H hdraw (by
        intro G hHG hGdraw hGnotconn
        exact WilliamsonShmoys.planar_drawing_add_edge_extension_1f6216d4_7176_426b_8eb5_1d4c84c6c67c
          G hGdraw hGnotconn)
  refine ⟨K, hsub, hconn, hdrawK, ?_⟩
  exact Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hsub) (Set.toFinite K.edgeSet)
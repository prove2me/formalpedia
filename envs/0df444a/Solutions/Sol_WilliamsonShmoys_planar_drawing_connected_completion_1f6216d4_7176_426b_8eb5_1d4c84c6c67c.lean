-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_completion_1f6216d4_7176_426b_8eb5_1d4c84c6c67c
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T02:10:38.18972+00:00
-- url     : https://prove2.me/submissions/1648370c-8882-4a8d-972f-79ee7d2579cb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_completion_core

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
    WilliamsonShmoys.planar_drawing_connected_completion_core H hdraw
  refine ⟨K, hsub, hconn, hdrawK, ?_⟩
  exact Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hsub) (Set.toFinite K.edgeSet)
-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_upper_bound_for_maximal_drawing_graph_584c8b76
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T01:35:34.635997+00:00
-- url     : https://prove2.me/submissions/4a3fa7f9-fef6-470a-9737-8a1e9aebec57
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_completion

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M) :
    M.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨K, _hMK, _hKDraw, hle, hKcard⟩ :=
    WilliamsonShmoys.planar_drawing_edge_count_completion
      M hDraw hV
  have hleInt : (M.edgeSet.ncard : Int) ≤ (K.edgeSet.ncard : Int) := by
    exact_mod_cast hle
  rw [hKcard] at hleInt
  omega
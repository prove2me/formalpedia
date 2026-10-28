-- Prove2me | solution 1 for WilliamsonShmoys.planar_completion_edge_count_for_maximal_edge_lower_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T07:20:24.046814+00:00
-- url     : https://prove2.me/submissions/6c384512-750e-4c68-ae18-930517e25fb7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_extension_to_maximal_drawing
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_for_completion

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ K : SimpleGraph V,
      N.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hNK, hK, hmax⟩ :=
    WilliamsonShmoys.planar_extension_to_maximal_drawing N hN
  have hcount :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count_for_completion K hV hK hmax
  exact ⟨K, hNK, hK, hcount⟩
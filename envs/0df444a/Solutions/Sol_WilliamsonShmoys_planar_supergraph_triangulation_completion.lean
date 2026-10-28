-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_triangulation_completion
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T07:06:47.91598+00:00
-- url     : https://prove2.me/submissions/d04dc543-3aaf-4a3b-94b2-77cd34021d71
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_edge_maximal_supergraph_776f5703
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_euler_edge_count_776f5703
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hHK, hK, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_has_edge_maximal_supergraph_776f5703 H hH
  exact ⟨K, hHK, hK,
    WilliamsonShmoys.maximal_planar_drawing_euler_edge_count_776f5703 K hV hK hmax⟩
-- Prove2me | solution 1 for WilliamsonShmoys.exists_triangulated_planar_supergraph_of_planar_drawing
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T11:19:34.706803+00:00
-- url     : https://prove2.me/submissions/e82294ae-2def-4a62-b97f-555f41b1ad9f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_extension_for_threshold
import Theorems.Thm_WilliamsonShmoys_edge_count_lower_bound_of_maximal_planar_drawing_via_threshold_euler

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    Exists fun M : SimpleGraph V => L <= M /\
      WilliamsonShmoys.HasPlanarDrawingOn M /\
      3 * Fintype.card V - 6 <= M.edgeSet.ncard := by
  obtain ⟨M, hLM, hM, hmax⟩ :=
    WilliamsonShmoys.exists_edge_maximal_planar_extension_for_threshold L hL
  exact ⟨M, hLM, hM,
    WilliamsonShmoys.edge_count_lower_bound_of_maximal_planar_drawing_via_threshold_euler M hV hM hmax⟩
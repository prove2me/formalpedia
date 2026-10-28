-- Prove2me | solution 1 for WilliamsonShmoys.planar_completion_edge_count_57da26e6_40fa_4eeb_a0ea_166241e54306
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T13:27:34.404351+00:00
-- url     : https://prove2.me/submissions/11a5842f-a5b8-44fa-b57a-467e275712bb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_for_edge_count_1794ae85_4ddf_4fc1_b226_9d54b8be81b3
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_1794ae85_4ddf_4fc1_b226_9d54b8be81b3

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ K : SimpleGraph V,
      N ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hNK, hK, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension_for_edge_count_1794ae85_4ddf_4fc1_b226_9d54b8be81b3 N hN
  have hCount := WilliamsonShmoys.maximal_planar_drawing_edge_count_1794ae85_4ddf_4fc1_b226_9d54b8be81b3
    K hK hV hMax
  exact ⟨K, hNK, hK, hCount⟩
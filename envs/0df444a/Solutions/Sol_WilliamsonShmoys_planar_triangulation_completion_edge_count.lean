-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_completion_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T05:05:07.354773+00:00
-- url     : https://prove2.me/submissions/b086b715-f91e-4546-bb70-72a7688292db
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_completion_exists_maximal_e9ce3df1_a197_4828_a24c_84c363604464
import Theorems.Thm_WilliamsonShmoys_maximal_drawing_edge_count_e9ce3df1_a197_4828_a24c_84c363604464
import Mathlib.Combinatorics.SimpleGraph.Basic

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      3 * Fintype.card V = L.edgeSet.ncard + 6 := by
  obtain ⟨L, hKL, hL, hmax⟩ :=
    WilliamsonShmoys.planar_completion_exists_maximal_e9ce3df1_a197_4828_a24c_84c363604464 K hV hK
  exact ⟨L, hKL, hL,
    WilliamsonShmoys.maximal_drawing_edge_count_e9ce3df1_a197_4828_a24c_84c363604464 L hV hL hmax⟩
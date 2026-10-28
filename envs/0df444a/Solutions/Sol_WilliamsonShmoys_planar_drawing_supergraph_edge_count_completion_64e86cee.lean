-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_supergraph_edge_count_completion_64e86cee
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T12:17:29.486527+00:00
-- url     : https://prove2.me/submissions/3e66ab59-e923-4497-adc7-4b006ffb912f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph_98108dba_1927_4e81_b6e3_ce95ad278038
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_98108dba_1927_4e81_b6e3_ce95ad278038
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K <= L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hKL, hL, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_supergraph_98108dba_1927_4e81_b6e3_ce95ad278038 K hK
  exact ⟨L, hKL, hL,
    WilliamsonShmoys.maximal_planar_drawing_edge_count_98108dba_1927_4e81_b6e3_ce95ad278038 L hV hL hmax⟩
-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_triangulation_completion_aa4e0804
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T13:01:19.924375+00:00
-- url     : https://prove2.me/submissions/3414afec-a787-4f14-b5db-260a3b7b62ad

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_maximal_extension
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_maximal_has_three_n_minus_six

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    Exists fun H : SimpleGraph V =>
      G <= H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨H, hGH, hH, hmax⟩ :=
    WilliamsonShmoys.planar_edge_count_maximal_extension G hV hG
  exact ⟨H, hGH, hH,
    WilliamsonShmoys.planar_edge_count_maximal_has_three_n_minus_six H hV hH hmax⟩
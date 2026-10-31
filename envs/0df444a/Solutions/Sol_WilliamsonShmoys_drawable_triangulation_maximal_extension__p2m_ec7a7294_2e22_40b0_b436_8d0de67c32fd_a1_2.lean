-- Prove2me | solution 2 for WilliamsonShmoys.drawable_triangulation_maximal_extension__p2m_ec7a7294_2e22_40b0_b436_8d0de67c32fd_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:46:31.241785+00:00
-- url     : https://prove2.me/submissions/d9458517-8a1f-4800-9b0d-592861850ae5

import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_saturated_extension_for_maximal_edge_count_retry2

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V, L ≤ M →
        WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ L :=
  WilliamsonShmoys.planar_drawing_edge_saturated_extension_for_maximal_edge_count_retry2 K hV hK

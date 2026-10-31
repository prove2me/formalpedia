-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_has_triangulated_completion__p2m_2881ff5d_60b0_4f02_aa50_a31ff757101b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:34:24.309+00:00
-- url     : https://prove2.me/submissions/87ba9a3e-f216-45b3-ab90-4882e41f54a1

import Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph_exact_edge_count

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ K : SimpleGraph V,
      N ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        3 * Fintype.card V - 6 = K.edgeSet.ncard :=
  WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count N hV hN

-- Prove2me | solution 2 for WilliamsonShmoys.planar_triangulation_completion__p2m_3060859a_0839_41c9_be06_b54269f75aee_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:19:53.278289+00:00
-- url     : https://prove2.me/submissions/3c2819d7-4e6d-47e6-ab2b-d4cd75edf4f4

import Theorems.Thm_WilliamsonShmoys_planar_supergraph_with_sharp_edge_count__p2m_4dcc8868_a279_4e00_9c27_a17d1a75556d_a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hPlanar : HasPlanarDrawingOn J) :
    ∃ N : SimpleGraph V,
      J ≤ N ∧
      HasPlanarDrawingOn N ∧
      3 * Fintype.card V - 6 = N.edgeSet.ncard :=
  WilliamsonShmoys.planar_supergraph_with_sharp_edge_count__p2m_4dcc8868_a279_4e00_9c27_a17d1a75556d_a1 J hV hPlanar

-- Prove2me | solution 2 for WilliamsonShmoys.maximalPlanar_edge_count__p2m_252969a2_5705_4ea9_b97e_d995b4f5b608_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:23:33.659486+00:00
-- url     : https://prove2.me/submissions/9227d7a8-d84a-451c-bb59-d6520b3d0626

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_43062042_0cdc_4c51_9c62_1a9950b577b3_a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M) (hMax : ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N = M) (hV : 3 ≤ Fintype.card V) : M.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  WilliamsonShmoys.maximal_planar_edge_count__p2m_43062042_0cdc_4c51_9c62_1a9950b577b3_a1 M hDraw hMax hV

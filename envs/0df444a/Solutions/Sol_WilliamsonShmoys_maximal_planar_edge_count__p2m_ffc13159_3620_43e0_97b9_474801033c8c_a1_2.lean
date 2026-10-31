-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_count__p2m_ffc13159_3620_43e0_97b9_474801033c8c_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:35:01.643129+00:00
-- url     : https://prove2.me/submissions/e5804631-e49b-4079-ba34-a95546a5fbf4

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_euler_7e0405ab

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L) (hV : 3 ≤ Fintype.card V) (hMax : ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ L) : L.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  WilliamsonShmoys.maximal_planar_edge_count_euler_7e0405ab L hDraw hV hMax

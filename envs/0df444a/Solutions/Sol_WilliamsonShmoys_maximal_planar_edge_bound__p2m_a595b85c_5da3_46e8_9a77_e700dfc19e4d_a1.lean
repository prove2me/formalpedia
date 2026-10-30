-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_bound__p2m_a595b85c_5da3_46e8_9a77_e700dfc19e4d_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:20:22.276816+00:00
-- url     : https://prove2.me/submissions/63f39deb-2a2c-4d12-aec4-c6af7569e4a0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound__p2m_fa1358d7_5b01_463f_a67b_1e1bbf77dca7_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V)
    (hMaximal : ∀ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn K → K.edgeSet ⊆ H.edgeSet) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  exact WilliamsonShmoys.planar_edge_bound__p2m_fa1358d7_5b01_463f_a67b_1e1bbf77dca7_a1
    H hH hCard
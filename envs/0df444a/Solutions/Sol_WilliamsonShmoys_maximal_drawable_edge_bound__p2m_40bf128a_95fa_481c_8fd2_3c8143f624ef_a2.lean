-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_bound__p2m_40bf128a_95fa_481c_8fd2_3c8143f624ef_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:47:15.210658+00:00
-- url     : https://prove2.me/submissions/d0bb35bf-f558-4cbb-b411-37c05dc034f3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawable_edge_bound__p2m_0dbc0e8c_fa05_4723_8a04_9065a5432a04_a2

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMax : ∀ N : SimpleGraph V, H ≤ N →
      WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ H) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  exact WilliamsonShmoys.planar_drawable_edge_bound__p2m_0dbc0e8c_fa05_4723_8a04_9065a5432a04_a2
    H hV hDraw
-- Prove2me | solution 1 for WilliamsonShmoys.edgeMaximalPlanar_edgeCount__p2m_dcc74752_2897_43b5_8a61_1f7227b8dfbf_a3__p2m_dcc74752_2897_43b5_8a61_1f7227b8dfbf_a4
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:58:48.714754+00:00
-- url     : https://prove2.me/submissions/56966737-7df0-4e35-8872-671c330adb8a

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarEdgeCountUpper__p2m_9fa2e1cf_f812_43a2_8937_813b0958a481_a1
import Theorems.Thm_WilliamsonShmoys_edgeMaximalPlanar_edgeCountLower__p2m_9fa2e1cf_f812_43a2_8937_813b0958a481_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hDraw : HasPlanarDrawingOn N)
    (hMax : ∀ M : SimpleGraph V, N ≤ M → HasPlanarDrawingOn M → M = N) :
    N.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper := WilliamsonShmoys.planarEdgeCountUpper__p2m_9fa2e1cf_f812_43a2_8937_813b0958a481_a1 N hV hDraw
  have hLower := WilliamsonShmoys.edgeMaximalPlanar_edgeCountLower__p2m_9fa2e1cf_f812_43a2_8937_813b0958a481_a1 N hV hDraw hMax
  omega
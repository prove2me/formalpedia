-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_eb26a690_3fb7_4c37_81bf_9f642ccd4501_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:04:13.161187+00:00
-- url     : https://prove2.me/submissions/d1fc6e20-a568-4216-a7a5-d564688a2ad2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper_bound__p2m_71827a3a_7db4_46f3_80ab_2c37e012e77b_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower_bound__p2m_71827a3a_7db4_46f3_80ab_2c37e012e77b_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 <= Fintype.card V)
    (hmax : ∀ M' : SimpleGraph V, M ≤ M' →
      WilliamsonShmoys.HasPlanarDrawingOn M' → M' = M) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hupper :=
    WilliamsonShmoys.planar_drawing_edge_count_upper_bound__p2m_71827a3a_7db4_46f3_80ab_2c37e012e77b_a2
      M hplanar hcard
  have hlower :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound__p2m_71827a3a_7db4_46f3_80ab_2c37e012e77b_a2
      M hplanar hcard hmax
  omega
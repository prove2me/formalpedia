-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_upper_bound__p2m_8b804cdd_68ca_48da_bde7_dd4a5c81f51a_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:52:41.837861+00:00
-- url     : https://prove2.me/submissions/3d806e2d-b702-4e2b-b5c0-d33453a4c2de

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_eb26a690_3fb7_4c37_81bf_9f642ccd4501_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_eb26a690_3fb7_4c37_81bf_9f642ccd4501_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 <= Fintype.card V) :
    N.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨M, hle, hMplanar, hMmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension__p2m_eb26a690_3fb7_4c37_81bf_9f642ccd4501_a1
      N hplanar hcard
  have hMcount :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_eb26a690_3fb7_4c37_81bf_9f642ccd4501_a1
      M hMplanar hcard hMmax
  omega
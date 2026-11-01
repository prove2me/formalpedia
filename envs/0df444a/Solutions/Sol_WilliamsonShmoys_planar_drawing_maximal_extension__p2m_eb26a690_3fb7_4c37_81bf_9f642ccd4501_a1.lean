-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension__p2m_eb26a690_3fb7_4c37_81bf_9f642ccd4501_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:06:29.089902+00:00
-- url     : https://prove2.me/submissions/5bf8b91e-54f2-42ce-8299-691b21ece52a

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_simpleGraph_extension__p2m_1ac9c334_525d_486c_82db_79a23d6eb9e0_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V,
      N.edgeSet.ncard ≤ M.edgeSet.ncard ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      (∀ M' : SimpleGraph V, M ≤ M' →
        WilliamsonShmoys.HasPlanarDrawingOn M' → M' = M) := by
  obtain ⟨M, hcount, hNM, hM, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_simpleGraph_extension__p2m_1ac9c334_525d_486c_82db_79a23d6eb9e0_a2
      N WilliamsonShmoys.HasPlanarDrawingOn hplanar
  exact ⟨M, hcount, hM, fun M' hMM' hM' => hmax M' hMM' hM'⟩
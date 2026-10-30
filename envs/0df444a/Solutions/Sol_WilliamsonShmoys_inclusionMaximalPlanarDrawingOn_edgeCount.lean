-- Prove2me | solution 1 for WilliamsonShmoys.inclusionMaximalPlanarDrawingOn_edgeCount
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T12:57:38.805995+00:00
-- url     : https://prove2.me/submissions/e09ebb90-52ae-4c81-a901-59a475f2de41

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_edgeSet_ncard_le
import Theorems.Thm_WilliamsonShmoys_inclusionMaximalPlanarDrawingOn_edgeSet_ncard_ge

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V,
      M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N = M) :
    3 * Fintype.card V - 6 = M.edgeSet.ncard := by
  have hle := WilliamsonShmoys.planarDrawingOn_edgeSet_ncard_le M hV hM
  have hge := WilliamsonShmoys.inclusionMaximalPlanarDrawingOn_edgeSet_ncard_ge M hV hM hmax
  omega
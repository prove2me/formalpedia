-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_5ed93e11_5366_47c6_a614_dcb01ec690c9_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:58:55.960613+00:00
-- url     : https://prove2.me/submissions/89122ef0-10e0-4adb-9d65-4c89af9a62a1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_connected_edge_count_completion__p2m_1758d6ea_f3f8_4fd3_af35_9019f186c486_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : ∀ N : SimpleGraph V, M ≤ N →
      WilliamsonShmoys.HasPlanarDrawingOn N → N = M)
    (hConn : M.Connected)
    (hV : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨H, hMH, hHdraw, hHcount⟩ :=
    WilliamsonShmoys.planar_connected_edge_count_completion__p2m_1758d6ea_f3f8_4fd3_af35_9019f186c486_a1
      M hM hConn hV
  have hHM : H = M := hMax H hMH hHdraw
  simpa [hHM] using hHcount
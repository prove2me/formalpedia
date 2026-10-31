-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_augmentation
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T00:15:18.769497+00:00
-- url     : https://prove2.me/submissions/30787810-23fa-447d-b30a-6316711891ac

import Theorems.Thm_WilliamsonShmoys_planar_drawing_spanning_tree_extension

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ H : SimpleGraph V,
      (∀ u v, L.Adj u v → H.Adj u v) ∧
      H.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      L.edgeSet.ncard ≤ H.edgeSet.ncard := by
  obtain ⟨H, T, hLH, hTconn, hTH, hHdraw, hCard⟩ :=
    WilliamsonShmoys.planar_drawing_spanning_tree_extension L hV hL
  have hHconn : H.Connected := hTconn.mono hTH
  exact ⟨H, hLH, hHconn, hHdraw, hCard⟩

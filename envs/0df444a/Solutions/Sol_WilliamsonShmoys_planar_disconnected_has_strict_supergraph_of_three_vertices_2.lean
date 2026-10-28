-- Prove2me | solution 2 for WilliamsonShmoys.planar_disconnected_has_strict_supergraph_of_three_vertices
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T08:12:32.295046+00:00
-- url     : https://prove2.me/submissions/8860a98c-9a55-4af7-a34d-5cb0efa0ad8a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_disconnected_has_connected_planar_supergraph_of_three_vertices
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hDisconnected : ¬ G.Connected) :
    ∃ H : SimpleGraph V,
      G < H ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by
  obtain ⟨H, hGH, hConnected, hH⟩ :=
    WilliamsonShmoys.planar_disconnected_has_connected_planar_supergraph_of_three_vertices
      G hV hG hDisconnected
  exact ⟨H, hGH, hH⟩
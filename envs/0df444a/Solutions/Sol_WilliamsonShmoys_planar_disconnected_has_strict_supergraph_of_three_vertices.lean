-- Prove2me | solution 1 for WilliamsonShmoys.planar_disconnected_has_strict_supergraph_of_three_vertices
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T08:00:54.988569+00:00
-- url     : https://prove2.me/submissions/b0623b2c-d3f4-4b16-aa7f-1d6041741d5a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_disconnected_has_connected_planar_supergraph
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hDisconnected : ¬ G.Connected) :
    ∃ H : SimpleGraph V,
      G < H ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by
  obtain ⟨H, hh⟩ :=
    WilliamsonShmoys.planar_disconnected_has_connected_planar_supergraph
      G hG hDisconnected
  rcases hh with ⟨hGH, hh⟩
  rcases hh with ⟨hConnected, hH⟩
  exact ⟨H, hGH, hH⟩

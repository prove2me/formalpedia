-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_bound_extension_core
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T13:28:23.531538+00:00
-- url     : https://prove2.me/submissions/fc70bfb6-b39e-4d80-b97d-409bd5c84956
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_maximal_extension_8a86a385
import Theorems.Thm_WilliamsonShmoys_planar_maximal_edge_count_8a86a385

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hConn : G.Connected)
    (hGdraw : HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, G ≤ H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨H, hGH, hHConn, hHdraw, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_edge_maximal_extension_8a86a385 G hConn hGdraw
  exact ⟨H, hGH,
    WilliamsonShmoys.planar_maximal_edge_count_8a86a385 H hHConn hHdraw hCard hMax⟩